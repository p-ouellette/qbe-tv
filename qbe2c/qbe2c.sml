structure Qbe2C =
struct

  structure AM = AtomMap
  structure T = QbeTypes
  structure PR32 = PackReal32Little
  structure PR64 = PackReal64Little
  structure PW32 = PackWord32Little
  structure PW64 = PackWord64Little
  structure TIO = TextIO

  exception Impossible

  datatype ctype = I32 | U32 | I64 | U64 | FLT | DBL

  fun impossible msg =
        (app (fn s => TIO.output(TIO.stdErr, s)) ["error: ", msg, "\n"];
         raise Impossible)

  fun canon ({name, linkage, params, envp, variadic, result=NONE, blocks}) = let
        fun findret ([]: T.block list) = NONE
          | findret ({jump=SOME(T.Retw _), ...} :: _) = SOME T.W
          | findret (_::bs) = findret bs
        fun fixret {label, phis, stmts, jump=SOME(T.Retw v)} =
              {label=label, phis=phis, stmts=stmts, jump=SOME(T.Ret v)}
          | fixret b = b
        val result = findret blocks
        val blocks = map fixret blocks
        in
          {name=name, linkage=linkage, params=params, envp=envp,
           variadic=variadic, result=result, blocks=blocks}
        end
    | canon f = f

  fun say out s = TIO.output(out, s)

  fun sayid out id = say out (Atom.toString id)

  fun ctype T.W = U32
    | ctype T.L = U64
    | ctype T.S = FLT
    | ctype T.D = DBL
    | ctype _ = impossible "base type expected"

  fun sayty out = (say out) o
        (fn I32 => "int32_t"
          | U32 => "uint32_t"
          | I64 => "int64_t"
          | U64 => "uint64_t"
          | FLT => "float"
          | DBL => "double")

  local
    val fixsign = String.map (fn #"~" => #"-" | c => c)

    val i64tolw = LargeWord.fromLargeInt o Int64.toLarge

    fun i64tor32 i = let
          val b = Word8Array.array(4, 0w0)
           in PW32.update(b, 0, i64tolw i);
              PR32.fromBytes(Word8Array.vector b)
          end

    fun i64tor64 i = let
          val b = Word8Array.array(8, 0w0)
           in PW64.update(b, 0, i64tolw i);
              PR64.fromBytes(Word8Array.vector b)
          end

    fun r32tolw r = PW32.subVec(PR32.toBytes r, 0)
    fun r64tolw r = PW64.subVec(PR64.toBytes r, 0)

    val r64tor32 = PR32.fromBytes o PR64.toBytes
  in
    fun saycon out ty c = let
          val say = say out
          val sayi64 = say o fixsign o Int64.toString
          val sayr32 = say o fixsign o Real32.toString
          val sayr64 = say o fixsign o Real64.toString
          val saylw = say o (LargeWord.fmt StringCvt.DEC)

          fun sayint (T.Int i) = sayi64 i
            | sayint (T.Flts r) = saylw (r32tolw r)
            | sayint (T.Fltd r) = saylw (r64tolw r)
          fun sayflt (T.Int i) = sayr32 (i64tor32 i)
            | sayflt (T.Flts r) = sayr32 r
            | sayflt (T.Fltd r) = sayr32 (r64tor32 r)
          fun saydbl (T.Int i) = sayr64 (i64tor64 i)
            | saydbl (T.Flts r) = sayr32 r
            | saydbl (T.Fltd r) = sayr64 r
          in
            case ty
              of I32 => (say "(int32_t)"; sayint c)
               | U32 => (say "(uint32_t)"; sayint c)
               | I64 => (say "(int64_t)"; sayint c)
               | U64 => (say "(uint64_t)"; sayint c)
               | FLT => (sayflt c; say "f")
               | DBL => saydbl c
          end
  end

  fun sayval out venv ty (T.Tmp name) =
        (case (ty, AM.lookup(venv, name))
           of (U32, U64) => (say out "(uint32_t)"; sayid out name)
            | (ty, ty') => if ty = ty' then sayid out name
                           else impossible "type mismatch")
    | sayval out venv ty (T.Glo name) = sayid out name
    | sayval out venv ty (T.Con c) = saycon out ty c

  fun trinstr out venv cls = let
    val ty = ctype cls
    val say = say out
    val sayval = sayval out venv
    fun sayv v = sayval ty v
    fun sayvs v = sayval (case ty of U32 => I32 | U64 => I64 | ty => ty) v
    in
      fn T.Add(a, b) => (sayv a; say " + "; sayv b)
       | T.Sub(a, b) => (sayv a; say " - "; sayv b)
       | T.Div(a, b) => (sayvs a; say " / "; sayvs b)
       | T.Mul(a, b) => (sayv a; say " * "; sayv b)
       | T.Neg a => (say "-"; sayv a)
       | T.Udiv(a, b) => (sayv a; say " / "; sayv b)
       | T.Rem(a, b) => (sayvs a; say " % "; sayvs b)
       | T.Urem(a, b) => (sayv a; say " % "; sayv b)
       | T.Or(a, b) => (sayv a; say " | "; sayv b)
       | T.Xor(a, b) => (sayv a; say " ^ "; sayv b)
       | T.And(a, b) => (sayv a; say " & "; sayv b)
       | T.Sar(a, b) => (sayvs a; say " >> "; say "("; sayv b;
                         say (case cls of T.W => " & 31)" | T.L => " & 63)"))
       | T.Shr(a, b) => (sayv a; say " >> "; say "("; sayv b;
                         say (case cls of T.W => " & 31)" | T.L => " & 63)"))
       | T.Shl(a, b) => (sayv a; say " << "; say "("; sayv b;
                         say (case cls of T.W => " & 31)" | T.L => " & 63)"))
       | T.Loadd a => say "loadd"
       | T.Loads a => say "loads"
       | T.Loadl a => say "loadl"
       | T.Loadw a => say "loadw"
       | T.Loadsw a => say "loadsw"
       | T.Loaduw a => say "loaduw"
       | T.Loadsh a => say "loadsh"
       | T.Loaduh a => say "loaduh"
       | T.Loadsb a => say "loadsb"
       | T.Loadub a => say "loadub"
       | T.Alloc4 a => say "alloc4"
       | T.Alloc8 a => say "alloc8"
       | T.Alloc16 a => say "alloc16"
       | T.Ceqd(a, b) => (sayv a; say " == "; sayv b)
       | T.Ceql(a, b) => (sayv a; say " == "; sayv b)
       | T.Ceqs(a, b) => (sayv a; say " == "; sayv b)
       | T.Ceqw(a, b) => (sayv a; say " == "; sayv b)
       | T.Cged(a, b) => (sayv a; say " >= "; sayv b)
       | T.Cges(a, b) => (sayv a; say " >= "; sayv b)
       | T.Cgtd(a, b) => (sayv a; say " > "; sayv b)
       | T.Cgts(a, b) => (sayv a; say " > "; sayv b)
       | T.Cled(a, b) => (sayv a; say " <= "; sayv b)
       | T.Cles(a, b) => (sayv a; say " <= "; sayv b)
       | T.Cltd(a, b) => (sayv a; say " < "; sayv b)
       | T.Clts(a, b) => (sayv a; say " < "; sayv b)
       | T.Cned(a, b) => (sayv a; say " != "; sayv b)
       | T.Cnel(a, b) => (sayv a; say " != "; sayv b)
       | T.Cnes(a, b) => (sayv a; say " != "; sayv b)
       | T.Cnew(a, b) => (sayv a; say " != "; sayv b)
       | T.Cod(a, b) => (sayv a; say " < "; sayv b; say " || ";
                         sayv a; say " >= "; sayv b)
       | T.Cos(a, b) => (sayv a; say " < "; sayv b; say " || ";
                         sayv a; say " >= "; sayv b)
       | T.Csgel(a, b) => (sayvs a; say " >= "; sayvs b)
       | T.Csgew(a, b) => (sayvs a; say " >= "; sayvs b)
       | T.Csgtl(a, b) => (sayvs a; say " > "; sayvs b)
       | T.Csgtw(a, b) => (sayvs a; say " > "; sayvs b)
       | T.Cslel(a, b) => (sayvs a; say " <= "; sayvs b)
       | T.Cslew(a, b) => (sayvs a; say " <= "; sayvs b)
       | T.Csltl(a, b) => (sayvs a; say " < "; sayvs b)
       | T.Csltw(a, b) => (sayvs a; say " < "; sayvs b)
       | T.Cugel(a, b) => (sayv a; say " >= "; sayv b)
       | T.Cugew(a, b) => (sayv a; say " >= "; sayv b)
       | T.Cugtl(a, b) => (sayv a; say " > "; sayv b)
       | T.Cugtw(a, b) => (sayv a; say " > "; sayv b)
       | T.Culel(a, b) => (sayv a; say " <= "; sayv b)
       | T.Culew(a, b) => (sayv a; say " <= "; sayv b)
       | T.Cultl(a, b) => (sayv a; say " < "; sayv b)
       | T.Cultw(a, b) => (sayv a; say " < "; sayv b)
       | T.Cuod(a, b) => (sayv a; say " != "; sayv a; say " || ";
                          sayv b; say " != "; sayv b)
       | T.Cuos(a, b) => (sayv a; say " != "; sayv a; say " || ";
                          sayv b; say " != "; sayv b)
       | T.Dtosi a => say "dtosi"
       | T.Dtoui a => say "dtoui"
       | T.Exts a => say "exts"
       | T.Extsb a => say "extsb"
       | T.Extsh a => say "extsh"
       | T.Extsw a => say "extsw"
       | T.Extub a => say "extub"
       | T.Extuh a => say "extuh"
       | T.Extuw a => say "extuw"
       | T.Sltof a => say "sltof"
       | T.Ultof a => say "ultof"
       | T.Stosi a => say "stosi"
       | T.Stoui a => say "stoui"
       | T.Swtof a => say "swtof"
       | T.Uwtof a => say "uwtof"
       | T.Truncd a => say "truncd"
       | T.Cast a => say "cast"
       | T.Copy a => say "copy"
       | T.Vaarg a => say "vaarg"
    end

  fun trassign out venv (name, ty, ins) = let
        val say = say out
        val ct = ctype ty
        val _ = say "\t"
        val (venv, ct') =
          case AM.find(venv, name)
            of NONE => ((sayty out ct; say " "; AM.insert(venv, name, ct)), ct)
             | SOME ct' => (venv, ct')
        in
          case (ct', ct)
            of (U32, U64) => (sayid out name; say " = ")
             | (U64, U32) => (say "*(uint32_t *)&"; sayid out name; say " = ")
             | _ => if ct' = ct then (sayid out name; say " = ")
                    else impossible "type mismatch";
          trinstr out venv ty ins; say ";\n";
          venv
        end

  fun trstmt out =
        fn (T.Assign a, venv) => trassign out venv a
         | (T.Stored a, venv) => (say out "\tstore\n"; venv)
         | (T.Stores a, venv) => (say out "\tstore\n"; venv)
         | (T.Storel a, venv) => (say out "\tstore\n"; venv)
         | (T.Storew a, venv) => (say out "\tstore\n"; venv)
         | (T.Storeh a, venv) => (say out "\tstore\n"; venv)
         | (T.Storeb a, venv) => (say out "\tstore\n"; venv)
         | (T.Call c, venv) => (say out "\tcall\n"; venv)
         | (T.Vastart v, venv) => (say out "\tvastart\n"; venv)
         | (T.Nop, venv) => venv

  fun trjmp out venv rty = let
        val say = say out
        val sayval = sayval out venv
        fun saygoto lbl = (say "goto "; sayid out lbl; say ";\n")
        in
          fn T.Jmp lbl => (say "\t"; saygoto lbl)
           | T.Jnz(v, l1, l2) => (say "\tif ("; sayval U32 v; say " != 0) ";
                                  saygoto l1; say "\t"; saygoto l2)
           | T.Ret NONE => say "\treturn;\n"
           | T.Ret(SOME v) => (say "\treturn "; sayval (ctype(valOf rty)) v;
                               say ";\n")
           | _ => impossible "unexpected ret"
        end

  fun trdef out (T.Data _) = ()
    | trdef out (T.Function func) = let
        val {name, params, result, blocks, ...} = canon func
        fun enterParam ((ty, name), venv) = AM.insert(venv, name, ctype ty)
        val venv = foldl enterParam AM.empty params
        val say = say out
        val sayty = sayty out
        fun sayparams [] = say "void"
          | sayparams [(ty, name)] = (sayty(ctype ty); say " "; sayid out name)
          | sayparams ((ty, name)::ps) =
              (sayty(ctype ty); say " "; sayid out name; say ", "; sayparams ps)
        fun trblk ({label, phis=_, stmts, jump}, venv) = let
              val _ = (sayid out label; say ":;\n")
              val venv = foldl (trstmt out) venv stmts
               in Option.app (trjmp out venv result) jump;
                  venv
              end
        in
          case result
            of NONE => say "void"
             | SOME ty => sayty(ctype ty);
          say " "; sayid out name; say "("; sayparams params; say ") {\n";
          foldl trblk venv blocks; say "}\n"
        end
    | trdef _ _ = ()

  fun qbe2c (ins, name) = let
        val defs = QbeParse.parse(ins, name)
        in
          if QbeParse.anyErrors() then OS.Process.failure
          else
            (say TIO.stdOut "#include <stdint.h>\n\n";
             app (trdef TIO.stdOut) defs;
             OS.Process.success)
        end

  fun main (_, []) = qbe2c(TIO.stdIn, "stdin")
    | main (_, [fileName]) = let
        val strm = TIO.openIn fileName
         in qbe2c(strm, fileName) before TIO.closeIn strm
        end
    | main _ = (TIO.output(TIO.stdErr, "usage: qbe2c [file.ssa]\n");
                OS.Process.failure)

end
