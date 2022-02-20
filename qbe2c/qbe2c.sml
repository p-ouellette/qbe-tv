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

  fun sayty out = (say out) o
        (fn T.W => "int"
          | T.L => "long"
          | T.S => "float"
          | T.D => "double"
          | _ => impossible "bad type")

  val fixsign = String.map (fn #"~" => #"-" | c => c)

  fun sayi32 out = (say out) o fixsign o Int32.toString
  fun sayi64 out = (say out) o fixsign o Int64.toString
  fun sayr32 out = (say out) o fixsign o Real32.toString
  fun sayr64 out = (say out) o fixsign o Real64.toString

  fun sayw32 out = (say out) o (Word32.fmt StringCvt.DEC)
  fun sayw64 out = (say out) o (Word64.fmt StringCvt.DEC)

  val i64toi32 = Int32.fromLarge o Word32.toLargeIntX
               o Word32.fromLargeInt o Int64.toLarge

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

  val r32tow32 = Word32.fromLarge o r32tolw
  val r64tow32 = Word32.fromLarge o r64tolw
  val r64tow64 = Word64.fromLarge o r64tolw

  val r64tor32 = PR32.fromBytes o PR64.toBytes

  fun saycon out =
    fn T.W => (fn T.Int i => sayi32 out (i64toi32 i)
                | T.Flts r => sayw32 out (r32tow32 r)
                | T.Fltd r => sayw32 out (r64tow32 r))
     | T.L => (fn T.Int i => sayi64 out i
                | T.Flts r => sayw32 out (r32tow32 r)
                | T.Fltd r => sayw64 out (r64tow64 r))
     | T.S => (fn T.Int i => sayr32 out (i64tor32 i)
                | T.Flts r => sayr32 out r
                | T.Fltd r => sayr32 out (r64tor32 r))
     | T.D => (fn T.Int i => sayr64 out (i64tor64 i)
                | T.Flts r => sayr32 out r
                | T.Fltd r => sayr64 out r)
     | _ => fn _ => impossible "bad type"

  fun sayval out venv ty (T.Tmp name) =
        (case (AM.lookup(venv, name), ty)
           of (T.L, T.W) => (say out "(int)"; sayid out name)
            | ts => if T.sameTy ts then sayid out name
                    else impossible "type mismatch")
    | sayval out venv ty (T.Glo name) = sayid out name
    | sayval out venv ty (T.Con c) = saycon out ty c

  fun trinstr out venv ty = let
    val say = say out
    val sayval = sayval out venv ty
    in
      fn T.Add(a, b) => (say "("; sayval a; say " + "; sayval b; say ")")
       | T.Sub(a, b) => (say "("; sayval a; say " - "; sayval b; say ")")
       | T.Div(a, b) => say "div"
       | T.Mul(a, b) => say "mul"
       | T.Neg a => say "neg"
       | T.Udiv(a, b) => say "udiv"
       | T.Rem(a, b) => say "rem"
       | T.Urem(a, b) => say "urem"
       | T.Or(a, b) => say "or"
       | T.Xor(a, b) => say "xor"
       | T.And(a, b) => say "and"
       | T.Sar(a, b) => say "sar"
       | T.Shr(a, b) => say "shr"
       | T.Shl(a, b) => say "shl"
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
       | T.Ceqd(a, b) => say "ceqd"
       | T.Ceql(a, b) => say "ceql"
       | T.Ceqs(a, b) => say "ceqs"
       | T.Ceqw(a, b) => say "ceqw"
       | T.Cged(a, b) => say "cged"
       | T.Cges(a, b) => say "cges"
       | T.Cgtd(a, b) => say "cgtd"
       | T.Cgts(a, b) => say "cgts"
       | T.Cled(a, b) => say "cled"
       | T.Cles(a, b) => say "cles"
       | T.Cltd(a, b) => say "cltd"
       | T.Clts(a, b) => say "clts"
       | T.Cned(a, b) => say "cned"
       | T.Cnel(a, b) => say "cnel"
       | T.Cnes(a, b) => say "cnes"
       | T.Cnew(a, b) => say "cnew"
       | T.Cod(a, b) => say "cod"
       | T.Cos(a, b) => say "cos"
       | T.Csgel(a, b) => say "csgel"
       | T.Csgew(a, b) => say "csgew"
       | T.Csgtl(a, b) => say "csgtl"
       | T.Csgtw(a, b) => say "csgtw"
       | T.Cslel(a, b) => say "cslel"
       | T.Cslew(a, b) => say "cslew"
       | T.Csltl(a, b) => say "csltl"
       | T.Csltw(a, b) => say "csltw"
       | T.Cugel(a, b) => say "cugel"
       | T.Cugew(a, b) => say "cugew"
       | T.Cugtl(a, b) => say "cugtl"
       | T.Cugtw(a, b) => say "cugtw"
       | T.Culel(a, b) => say "culel"
       | T.Culew(a, b) => say "culew"
       | T.Cultl(a, b) => say "cultl"
       | T.Cultw(a, b) => say "cultw"
       | T.Cuod(a, b) => say "cuod"
       | T.Cuos(a, b) => say "cuos"
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
        val _ = say "\t"
        val (venv, ty') =
          case AM.find(venv, name)
            of NONE => ((sayty out ty; say " "; AM.insert(venv, name, ty)), ty)
             | SOME ty' => (venv, ty')
        in
          case (ty', ty)
            of (T.W, T.L) => (sayid out name; say " = (int)")
             | (T.L, T.W) => (say "*(int *)&"; sayid out name; say " = ")
             | ts => if T.sameTy ts then (sayid out name; say " = ")
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
           | T.Jnz(v, l1, l2) => (say "\tif ("; sayval T.W v; say " != 0) ";
                                  saygoto l1; say "\t"; saygoto l2)
           | T.Ret NONE => say "\treturn;\n"
           | T.Ret(SOME v) => (say "\treturn "; sayval (valOf rty) v; say ";\n")
           | _ => impossible "unexpected ret"
        end

  fun trdef out (T.Data _) = ()
    | trdef out (T.Function func) = let
        val {name, params, result, blocks, ...} = canon func
        fun enterParam ((ty, name), venv) = AM.insert(venv, name, ty)
        val venv = foldl enterParam AM.empty params
        val say = say out
        fun sayparams [] = say "void"
          | sayparams [(ty, name)] = (sayty out ty; say " "; sayid out name)
          | sayparams ((ty, name)::ps) =
              (sayty out ty; say " "; sayid out name; say ", "; sayparams ps)
        fun trblk ({label, phis=_, stmts, jump}, venv) = let
              val _ = (sayid out label; say ":;\n")
              val venv = foldl (trstmt out) venv stmts
               in Option.app (trjmp out venv result) jump;
                  venv
              end
        in
          case result
            of NONE => say "void"
             | SOME ty => sayty out ty;
          say " "; sayid out name; say "("; sayparams params; say ") {\n";
          foldl trblk venv blocks; say "}\n"
        end
    | trdef _ _ = ()

  fun main (_, [fileName]) = let
        val defs = QbeParse.parse fileName
        in
          if QbeParse.anyErrors() then OS.Process.failure
          else (app (trdef TIO.stdOut) defs; OS.Process.success)
        end
    | main _ = (TIO.output(TIO.stdErr, "usage: qbe2c file\n");
                OS.Process.failure)

end
