structure Qbe2C =
struct

  structure AM = AtomMap
  structure AS = AtomSet
  structure T = QbeTypes
  structure PR32 = PackReal32Little
  structure PR64 = PackReal64Little
  structure PW32 = PackWord32Little
  structure PW64 = PackWord64Little
  structure TIO = TextIO

  datatype ctype = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64 | FLT | DBL
                 | MEM of int * T.value

  exception Impossible

  fun impossible msg =
        (app (fn s => TIO.output(TIO.stdErr, s)) ["error: ", msg, "\n"];
         raise Impossible)

  fun say out s = TIO.output(out, s)

  fun sayid out = (say out)
                o (String.map (fn #"." => #"_" | #"$" => #"_" | c => c))
                o Atom.toString

  fun ctype T.W = U32
    | ctype T.L = U64
    | ctype T.S = FLT
    | ctype T.D = DBL
    | ctype (T.Agg _) = U64
    | ctype _ = impossible "unexpected type"

  val sameCty =
    fn (I8, I8) => true
     | (U8, U8) => true
     | (I16, I16) => true
     | (U16, U16) => true
     | (I32, I32) => true
     | (U32, U32) => true
     | (I64, I64) => true
     | (U64, U64) => true
     | (FLT, FLT) => true
     | (DBL, DBL) => true
     | (MEM _, MEM _) => true
     | _ => false

  fun sayty out = let
    val say = say out
    in
      fn I8 => say "int8_t"
       | U8 => say "uint8_t"
       | I16 => say "int16_t"
       | U16 => say "uint16_t"
       | I32 => say "int32_t"
       | U32 => say "uint32_t"
       | I64 => say "int64_t"
       | U64 => say "uint64_t"
       | FLT => say "float"
       | DBL => say "double"
       | MEM(i, _) => (say "_Alignas("; say(Int.toString i); say ") uint8_t")
    end

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
              of FLT => (sayflt c; say "f")
               | DBL => saydbl c
               | MEM _ => impossible "unexpected MEM type"
               | _ => (say "("; sayty out ty; say ")"; sayint c)
          end
  end

  fun sayval out venv ty (T.Tmp name) = let
        val decty = AM.lookup(venv, name)
        in
          if sameCty(ty, decty) then sayid out name
          else (say out "("; sayty out ty; say out ")"; sayid out name)
        end
    | sayval out venv ty (T.Glo name) = sayid out name
    | sayval out venv ty (T.Con c) = saycon out ty c

  fun saymemval out (T.Tmp a) = sayid out a
    | saymemval out (T.Glo a) = sayid out a
    | saymemval out (T.Con c) = saycon out U64 c

  fun trassign out venv (name, ty) = let
        fun sayeq name = (sayid out name; say out " = ")
        in
          case (AM.lookup(venv, name), ctype ty)
            of (U32, U64) => sayeq name
             | (MEM _, U64) => sayeq name
             | (U64, U32) => (say out "*(uint32_t *)&"; sayeq name)
             | ts => if sameCty ts then sayeq name
                     else impossible "type mismatch"
        end

  fun trphi out venv {temp=(name, ty), args} = let
        val say = say out
        val sayval = sayval out venv (ctype ty)
        fun trargs [(_, v)] = sayval v
          | trargs ((l, v)::args) =
              (say "pred == "; sayid out l; say " ? "; sayval v;
               say " : "; trargs args)
        in
          say "\t"; trassign out venv (name, ty); trargs args; say ";\n"
        end

  fun trinstr out venv cls = let
    val ty = ctype cls
    val sty = case ty of U32 => I32 | U64 => I64 | ty => ty
    val castty = fn U32 => FLT | U64 => DBL | FLT => U32 | DBL => U64
    val say = say out
    val sayty = sayty out
    val sayval = sayval out venv
    fun sayv v = sayval ty v
    fun sayvs v = sayval sty v
    val sayi32 = sayval I32
    val sayu32 = sayval U32
    val sayi64 = sayval I64
    val sayu64 = sayval U64
    val sayflt = sayval FLT
    val saydbl = sayval DBL
    fun sayload ty v = (say "*("; sayty ty; say " *)"; saymemval out v)
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
       | T.Sar(a, b) => (sayvs a; say " >> "; say "("; sayu32 b;
                         say (case cls of T.W => " & 31)" | T.L => " & 63)"))
       | T.Shr(a, b) => (sayv a; say " >> "; say "("; sayu32 b;
                         say (case cls of T.W => " & 31)" | T.L => " & 63)"))
       | T.Shl(a, b) => (sayv a; say " << "; say "("; sayu32 b;
                         say (case cls of T.W => " & 31)" | T.L => " & 63)"))
       | T.Loadd a => sayload DBL a
       | T.Loads a => sayload FLT a
       | T.Loadl a => sayload U64 a
       | T.Loadw a => sayload I32 a
       | T.Loadsw a => sayload I32 a
       | T.Loaduw a => sayload U32 a
       | T.Loadsh a => sayload I16 a
       | T.Loaduh a => sayload U16 a
       | T.Loadsb a => sayload I8 a
       | T.Loadub a => sayload U8 a
       | T.Alloc4 _ => impossible "unexpected alloc"
       | T.Alloc8 _ => impossible "unexpected alloc"
       | T.Alloc16 _ => impossible "unexpected alloc"
       | T.Ceqd(a, b) => (saydbl a; say " == "; saydbl b)
       | T.Ceql(a, b) => (sayu64 a; say " == "; sayu64 b)
       | T.Ceqs(a, b) => (sayflt a; say " == "; sayflt b)
       | T.Ceqw(a, b) => (sayu32 a; say " == "; sayu32 b)
       | T.Cged(a, b) => (saydbl a; say " >= "; saydbl b)
       | T.Cges(a, b) => (sayflt a; say " >= "; sayflt b)
       | T.Cgtd(a, b) => (saydbl a; say " > "; saydbl b)
       | T.Cgts(a, b) => (sayflt a; say " > "; sayflt b)
       | T.Cled(a, b) => (saydbl a; say " <= "; saydbl b)
       | T.Cles(a, b) => (sayflt a; say " <= "; sayflt b)
       | T.Cltd(a, b) => (saydbl a; say " < "; saydbl b)
       | T.Clts(a, b) => (sayflt a; say " < "; sayflt b)
       | T.Cned(a, b) => (saydbl a; say " != "; saydbl b)
       | T.Cnel(a, b) => (sayu64 a; say " != "; sayu64 b)
       | T.Cnes(a, b) => (sayflt a; say " != "; sayflt b)
       | T.Cnew(a, b) => (sayu32 a; say " != "; sayu32 b)
       | T.Cod(a, b) => (saydbl a; say " < "; saydbl b; say " || ";
                         saydbl a; say " >= "; saydbl b)
       | T.Cos(a, b) => (sayflt a; say " < "; sayflt b; say " || ";
                         sayflt a; say " >= "; sayflt b)
       | T.Csgel(a, b) => (sayi64 a; say " >= "; sayi64 b)
       | T.Csgew(a, b) => (sayi32 a; say " >= "; sayi32 b)
       | T.Csgtl(a, b) => (sayi64 a; say " > "; sayi64 b)
       | T.Csgtw(a, b) => (sayi32 a; say " > "; sayi32 b)
       | T.Cslel(a, b) => (sayi64 a; say " <= "; sayi64 b)
       | T.Cslew(a, b) => (sayi32 a; say " <= "; sayi32 b)
       | T.Csltl(a, b) => (sayi64 a; say " < "; sayi64 b)
       | T.Csltw(a, b) => (sayi32 a; say " < "; sayi32 b)
       | T.Cugel(a, b) => (sayu64 a; say " >= "; sayu64 b)
       | T.Cugew(a, b) => (sayu32 a; say " >= "; sayu32 b)
       | T.Cugtl(a, b) => (sayu64 a; say " > "; sayu64 b)
       | T.Cugtw(a, b) => (sayu32 a; say " > "; sayu32 b)
       | T.Culel(a, b) => (sayu64 a; say " <= "; sayu64 b)
       | T.Culew(a, b) => (sayu32 a; say " <= "; sayu32 b)
       | T.Cultl(a, b) => (sayu64 a; say " < "; sayu64 b)
       | T.Cultw(a, b) => (sayu32 a; say " < "; sayu32 b)
       | T.Cuod(a, b) => (saydbl a; say " != "; saydbl a; say " || ";
                          saydbl b; say " != "; saydbl b)
       | T.Cuos(a, b) => (sayflt a; say " != "; sayflt a; say " || ";
                          sayflt b; say " != "; sayflt b)
       | T.Dtosi a => (say "("; sayty sty; say ")"; saydbl a)
       | T.Dtoui a => (say "("; sayty ty; say ")"; saydbl a)
       | T.Exts a => sayflt a
       | T.Extsb a => sayval I8 a
       | T.Extsh a => sayval I16 a
       | T.Extsw a => sayi32 a
       | T.Extub a => sayval U8 a
       | T.Extuh a => sayval U16 a
       | T.Extuw a => sayu32 a
       | T.Sltof a => (say "("; sayty ty; say ")"; sayi64 a)
       | T.Ultof a => (say "("; sayty ty; say ")"; sayu64 a)
       | T.Stosi a => (say "("; sayty sty; say ")"; sayflt a)
       | T.Stoui a => (say "("; sayty ty; say ")"; sayflt a)
       | T.Swtof a => (say "(float)"; sayi32 a)
       | T.Uwtof a => (say "(float)"; sayu32 a)
       | T.Truncd a => (say "(float)"; saydbl a)
       | T.Cast a => (say "(union { "; sayty (castty ty); say " a; "; sayty ty;
                      say " b; }){ .a = "; sayval (castty ty) a; say " }.b")
       | T.Copy a => sayv a
       | T.Vaarg a => say "vaarg"
    end

  fun trstmt out venv = let
        val say = say out
        fun trstore ty (v, m) =
              (say "\t*("; sayty out ty; say " *)"; saymemval out m; say " = ";
               sayval out venv ty v; say ";\n")
        fun trargs [] = ()
          | trargs [(ty, v)] = sayval out venv (ctype ty) v
          | trargs ((ty, v)::args) =
              (sayval out venv (ctype ty) v; say ", "; trargs args)
        in
          fn T.Assign(_, _, T.Alloc4 _) => ()
           | T.Assign(_, _, T.Alloc8 _) => ()
           | T.Assign(_, _, T.Alloc16 _) => ()
           | T.Assign(name, ty, ins) =>
               (say "\t"; trassign out venv (name, ty);
                trinstr out venv ty ins; say ";\n")
           | T.Stored a => trstore DBL a
           | T.Stores a => trstore FLT a
           | T.Storel a => trstore U64 a
           | T.Storew a => trstore U32 a
           | T.Storeh a => trstore U16 a
           | T.Storeb a => trstore U8 a
           | T.Call {result=NONE, name, args, ...} =>
               (say "\t"; sayid out name; say "("; trargs args; say ");\n")
           | T.Call {result=SOME r, name, args, ...} =>
               (say "\t"; trassign out venv r; sayid out name; say "(";
                trargs args; say ");\n")
           | T.Vastart v => say "\tvastart\n"
        end

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
        end

  fun enterDecs ({phis, stmts, ...}: T.block, venv) = let
        val enterDec = AM.insertWith (fn (v', v) => v')
        fun enterPhi ({temp=(name, ty), args=_}, venv) =
              enterDec(venv, name, ctype ty)
        fun enterStmt (stmt, venv) =
              case stmt
                of T.Assign(a, _, T.Alloc4 v) => enterDec(venv, a, MEM(4, v))
                 | T.Assign(a, _, T.Alloc8 v) => enterDec(venv, a, MEM(8, v))
                 | T.Assign(a, _, T.Alloc16 v) => enterDec(venv, a, MEM(16, v))
                 | T.Assign(a, ty, _) => enterDec(venv, a, ctype ty)
                 | T.Call {result=SOME(a, ty), ...} => enterDec(venv, a, ctype ty)
                 | _ => venv
        val venv = foldl enterPhi venv phis
         in foldl enterStmt venv stmts
        end

  fun saydecs out venv [] = ()
    | saydecs out venv (decs as (_, ty)::_) = let
        val say = say out
        fun saydec (name, MEM(_, n)) =
              (sayid out name; say "["; sayval out venv U64 n; say "]")
          | saydec (name, _) = sayid out name
        fun loop [d] = saydec d
          | loop (d::ds) = (saydec d; say ", "; loop ds)
         in say "\t"; sayty out ty; say " "; loop decs; say ";\n"
        end

  fun trdef out (T.Data _) = ()
    | trdef out (T.Function {name, params, result, blocks, ...}) = let
        val say = say out
        val sayty = sayty out
        val sayid = sayid out
        fun sayparams [] = say "void"
          | sayparams [(ty, name)] = (sayty(ctype ty); say " "; sayid name)
          | sayparams ((ty, name)::ps) =
              (sayty(ctype ty); say " "; sayid name; say ", "; sayparams ps)
        fun trblk venv plabs {label, phis, stmts, jump} =
              (sayid label; say ":\n";
               app (trphi out venv) phis;
               app (trstmt out venv) stmts;
               if AS.member(plabs, label) then
                 (say "\tpred = "; sayid label; say ";\n")
               else ();
               Option.app (trjmp out venv result) jump)
        fun enterParam ((ty, name), venv) = AM.insert(venv, name, ctype ty)
        val venvp = foldl enterParam AM.empty params
        val venvd = foldl enterDecs AM.empty blocks
        val venv = AM.unionWith (fn (p, d) => p) (venvp, venvd)
        fun ismem i (MEM(i', _)) = i = i'
          | ismem _ _ = false
        fun isty ty ty' = sameCty(ty, ty')
        val decGroups =
          map (fn f => List.filter (fn (_, t) => f t) (AM.listItemsi venvd))
            [ismem 4, ismem 8, ismem 16, isty U32, isty U64, isty FLT, isty DBL]
        fun philabs ({temp, args}, ls) =
              foldl (fn ((l, _), ls) => AS.add(ls, l)) ls args
        val plabs =
          foldl (fn ({phis, ...}, ls) => foldl philabs ls phis) AS.empty blocks
        in
          case result
            of NONE => say "void"
             | SOME ty => sayty(ctype ty);
          say " "; sayid name; say "("; sayparams params; say ") {\n";
          if AS.isEmpty plabs then () else
            (say "\tenum {\n";
             AS.app (fn l => (say "\t\t"; sayid l; say ",\n")) plabs;
             say "\t};\n";
             say "\tint pred;\n");
          app (saydecs out venv) decGroups;
          app (trblk venv plabs) blocks; say "}\n"
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
