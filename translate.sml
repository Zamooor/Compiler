signature TRANSLATE =
sig
    type level
    type access
type exp
type frag
    
    val outermost : level
    val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
    val formals: level -> access list
    val allocLocal: level-> bool -> access
    

    val opTree: Absyn.oper * exp * exp -> exp
    val assign: exp * exp -> exp
    val ifElse: exp * exp * exp -> exp
    val ifThen: exp * exp -> exp
    val whileTree: exp * exp * Temp.label -> exp
    val breakJump: Temp.label -> exp
    val call: Temp.label * Types.ty list -> exp
    val arrayConst: exp* exp -> exp
    val recordConst: exp list * Symbol.symbol list -> exp
    val seq: Tree.stm list -> exp
    val var: Symbol.symbol -> exp
    val recordVar: Symbol.symbol * exp -> exp
    val arrayVar: exp * exp -> exp
    
    
    val intConst: int -> exp
    val stringConst: string -> exp
    
    
end

structure Translate : TRANSLATE =
struct
    structure F = Amd64Frame
    structure T = Temp
    structure Tr = Tree
    structure A = Absyn
    
    datatype level = Top | Level of {parent: level, name: T.label, formals: bool list, frame: F.frame, unique: unit ref}
    datatype access = Access of (level * F.access)
datatype exp = Ex of Tree.exp
|	Nx of Tree.stm
|	Cx of Temp.label * Temp.label -> Tree.stm

    fun unEx (Ex e) = e
    | unEx (Cx genstm) =
        let
            val r = Temp.newtemp()
            val t = Temp.newlabel()
            val f = Temp.newlabel()
        in
            Tr.ESEQ(Tr.SEQ(Tr.MOVE(Tr.TEMP r, Tr.CONST 1),
                            Tr.SEQ(genstm(t,f),
                            Tr.SEQ(Tr.LABEL f,
                            Tr.SEQ(Tr.MOVE(Tr.TEMP r, Tr.CONST 0),
                            Tr.LABEL t)))),
                    Tr.TEMP r)
        end
    | unEx (Nx s) = Tr.ESEQ(s, Tr.CONST 0)
    
    fun unNx (Ex e) = Tr.EXP(e)
    | unNx (Cx genstm) = Tr.EXP(unEx(Cx(genstm)))
    | unNx (Nx stm) = stm
    
    fun unCx (Ex (Tr.CONST 0)) = (fn (l1, l2) => Tr.JUMP (Tr.NAME l2, [l2]))
    | unCx (Ex (Tr.CONST 1)) = (fn (l1, l2) => Tr.JUMP (Tr.NAME l1, [l1]))
    | unCx (Ex e) = (fn (l1, l2) => Tr.CJUMP (Tr.EQ, Tr.CONST 1, e, l1, l2))
    | unCx (Cx c) = c
    | unCx (Nx _) = ErrorMsg.impossible "SHOULD NEVER SEE THIS ERROR!!!!!"
    


type frag = F.frag
    
    val outermost = Top
    
    fun newLevel({parent, name, formals}) =
        Level{parent = parent, name = name, formals = formals, 
            frame = F.newFrame({name=name,formals=(true :: formals)}), unique = ref()}
    
        
    fun formals(level as Level{parent, name, formals, frame, unique}) =
    (
        case F.formals frame of [] =>
        (
            ErrorMsg.impossible "Frame has no formals";
            []
        )
        | _ :: formals => map (fn frameAccess => Access(level, frameAccess)) formals
    )
    | formals(Top) = []
    
    fun allocLocal (level as Level {parent, name, frame, formals, unique}) escapes = Access(level, F.allocLocal frame escapes)
    | allocLocal Top _ = ErrorMsg.impossible "Can't alloc in top frame"
    
    fun seq [] = Nx(Tr.EXP (Tr.CONST 0))
    | seq [stm1] = Nx(stm1)
    | seq (stm :: stms) = Nx(Tr.SEQ (stm, unNx(seq stms)))
    
    
    fun opTree(A.PlusOp, left, right) =
        Ex(Tr.BINOP(Tr.PLUS, unEx(left), unEx(right)))
    | opTree(A.MinusOp, left, right) = 
        Ex(Tr.BINOP(Tr.PLUS, unEx(left), unEx(right)))
    | opTree(A.TimesOp, left, right) = 
        Ex(Tr.BINOP(Tr.MUL, unEx(left), unEx(right)))
    | opTree(A.DivideOp, left, right) = 
        Ex(Tr.BINOP(Tr.DIV, unEx(left), unEx(right)))
    | opTree(A.EqOp, left, right) = 
        Cx(fn (t,f) => Tree.CJUMP(Tr.EQ, unEx(left), unEx(right), t, f))
    | opTree(A.NeqOp, left, right) = 
        Cx(fn (t,f) => Tree.CJUMP(Tr.NE, unEx(left), unEx(right), t, f))
    | opTree(A.LtOp, left, right)=
        Cx(fn (t,f) => Tree.CJUMP(Tr.LT, unEx(left), unEx(right), t, f))        
    | opTree(A.GtOp, left, right) = 
        Cx(fn (t,f) => Tree.CJUMP(Tr.GT, unEx(left), unEx(right), t, f))
    | opTree(A.LeOp, left, right) = 
        Cx(fn (t,f) => Tree.CJUMP(Tr.LE, unEx(left), unEx(right), t, f))
    | opTree(A.GeOp, left, right) = 
        Cx(fn (t,f) => Tree.CJUMP(Tr.GE, unEx(left), unEx(right), t, f))
        

    
    
    
    fun assign(lval, rexp) =
		Nx(Tr.MOVE(unEx(lval), unEx(rexp)))
    
    fun ifElse(test, then', else') =
        let
            val r = Temp.newtemp()
            val t = Temp.newlabel()
            val f = Temp.newlabel()
            val z = Temp.newlabel()
        in
            Ex(Tr.ESEQ
            (
                unNx(seq[unCx(test)(t,f),
                    Tr.LABEL(t),
                    Tr.MOVE(Tr.TEMP(r), unEx(then')),
                    Tr.JUMP(Tr.NAME z, [z]),
                    Tr.LABEL(f),
                    Tr.MOVE(Tr.TEMP(r), unEx(else')),
                    Tr.JUMP(Tr.NAME z, [z]),
                    Tr.LABEL(z)]),
                Tr.TEMP(r)
            ))
        end
        
    
    fun ifThen(test, then') =
        let
            val t = Temp.newlabel()
            val f = Temp.newlabel()
        in
            seq[unCx(test)(t,f),
                Tr.LABEL(t),
                unNx(then'),
                Tr.LABEL(f)]
        end

    
    fun whileTree(test, body, breakLab) =
		let
			val testLab = T.newlabel()
			val bodyLab = T.newlabel()
		in
			Nx(seq[Tr.LABEL(testLab),
					(unCx(test) (bodyLab, breakLab)),
					Tr.LABEL(bodyLab),
					(unNx(body)),
					Tr.JUMP(Tr.NAME(testLab), [testLab]),
					Tr.LABEL(breakLab)])
		end
    
    fun breakJump(breakLab) =
		Nx(Tr.JUMP(Tr.NAME(breakLab), [breakLab]))
    
    fun call(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun intConst(integer) = 
        Ex(Tr.CONST(integer))
        
    fun stringConst(str) =
		let
			val strLab = T.newlabel()
		in
			Ex(Tr.NAME strLab)
		end
        
    fun arrayConst(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun recordConst(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun seq(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun var(_) = ErrorMsg.impossible "UNIMPLEMENTED"
   
    fun islvlequal(Level{parent=_, name=_, formals=_, frame=_, unique=u1}, 
			Level{parent=_, name=_, formals=_, frame=_, unique=u2}) = (u1=u2)
	| islvlequal(_, _) = 
		ErrorMsg.impossible "Should never occure, variables can not be declared in Top"


    fun followstlink(deflevel, curlevel) = 
	(
	if(islvlequal(deflevel,curlevel))
	then Tr.TEMP(F.FP)
	else
		case 	curlevel
		of 	Level {parent, name, formals, frame, unique} => followstlink(deflevel,parent)
		|	TOP => (ErrorMsg.impossible "following static link reached top level")
	)	

    fun simpleVar(Access(varlevel, access), uselevel) =
		Ex( F.exp (access) (followstlink(varlevel,uselevel)) )
    
    (*fieldVar*)
    fun recordVar(varExp, indexExp) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    (*subscriptVar*)
    fun arrayVar(varExp, indexExp) = 
	Ex(Tr.MEM(Tree.BINOP(Tr.PLUS, 
				Tr.MEM(unEx(varExp)), 
				Tr.BINOP(Tr.MUL,
					unEx(indexExp),Tree.CONST(F.wordSize)))))
    
    
    
    
        
end
    
