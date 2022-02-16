structure Qbe2C =
struct

  structure T = QbeTypes
  structure TIO = TextIO

  exception InvalidAst

  fun canon ({name, linkage, params, envp, variadic, result=NONE, blocks}) = let
        fun findret ([]: T.block list) = NONE
          | findret ({jump=SOME(T.Retw _), ...} :: _) = SOME T.W
          | findret (_::bs) = findret bs
        fun fixret {label, stmts, jump=SOME(T.Retw v)} =
              {label=label, stmts=stmts, jump=SOME(T.Ret v)}
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

  fun basety T.W = "int"
    | basety T.L = "long"
    | basety T.S = "float"
    | basety T.D = "double"
    | basety _ = raise InvalidAst

  fun saybasety out = (say out) o basety

  fun saycon out (T.Int i) = say out (Int.toString i)
    | saycon out (T.Flts f) = say out (Real.toString f)
    | saycon out (T.Fltd f) = say out (Real.toString f)

  fun sayval out (T.Tmp name) = sayid out name
    | sayval out (T.Glo name) = sayid out name
    | sayval out (T.Con c) = saycon out c

  fun sayinstr out = let
    val say = say out
    val sayval = sayval out
    in
      fn T.Add(a, b) => (sayval a; say " + "; sayval b)
       | T.Sub(a, b) => (sayval a; say " - "; sayval b)
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
       | T.Stored(a, b) => say "stored"
       | T.Stores(a, b) => say "stores"
       | T.Storel(a, b) => say "storel"
       | T.Storew(a, b) => say "storew"
       | T.Storeh(a, b) => say "storeh"
       | T.Storeb(a, b) => say "storeb"
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
       | T.Call {name, args, ...} => say "copy"
       | T.Vastart a => say "vastart"
       | T.Vaarg a => say "vaarg"
       | T.Phi args => say "phi"
       | _ => raise Fail "impossible"
    end

  fun trdef out (T.Type _) = ()
    | trdef out (T.OpaqueType _) = ()
    | trdef out (T.Data _) = ()
    | trdef out (T.Function func) = let
        val say = say out
        fun sayparam (ty, name) =
              (saybasety out ty; say " "; sayid out name; say ", ")
        fun saystmt (T.Assign(name, ty, ins)) =
              (say "\t"; saybasety out ty; say " "; sayid out name; say " = ";
               sayinstr out ins; say ";\n")
          | saystmt (T.Volatile T.Nop) = ()
          | saystmt (T.Volatile ins) = (say "\t"; sayinstr out ins; say ";\n")
        fun saygoto l = (say "goto "; sayid out l; say ";\n")
        fun sayblk {label, stmts, jump} =
              (sayid out label; say ":;\n"; app saystmt stmts;
               case jump
                 of NONE => ()
                  | SOME(T.Jmp l) => (say "\t"; saygoto l)
                  | SOME(T.Jnz(v, l1, l2)) =>
                      (say "\tif ("; sayval out v; say " != 0) "; saygoto l1;
                       say "\t"; saygoto l2)
                  | SOME(T.Ret NONE) => say "\treturn;\n"
                  | SOME(T.Ret(SOME v)) =>
                      (say "\treturn "; sayval out v; say ";\n")
                  | _ => raise InvalidAst)
        val {name, params, result, blocks, ...} = canon func
        in
          case result
            of NONE => say "void"
             | SOME ty => saybasety out ty;
          say " "; sayid out name; say "(";
          case params
            of [] => say "void"
             | _ => app sayparam params;
          say ") {\n"; app sayblk blocks; say "}\n"
        end

  fun main (_, [fileName]) = let
        val defs = QbeParse.parse fileName
        in
          if QbeParse.anyErrors() then OS.Process.failure
          else (app (trdef TIO.stdOut) defs; OS.Process.success)
        end
    | main _ = (TIO.output(TIO.stdErr, "usage: qbe2c file\n");
                OS.Process.failure)

end
