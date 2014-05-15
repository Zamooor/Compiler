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
    
    val opTree: Absyn.oper * Tree.exp * Tree.exp -> Tree.exp
    val assign: Tree.exp * Tree.exp -> Tree.exp
    val ifElse: Tree.exp * Tree.exp * Tree.exp -> Tree.exp
    val ifThen: Tree.exp * Tree.exp -> Tree.exp
    val whileTree: Tree.exp * Tree.exp -> Tree.exp
    val breakJump: Temp.label -> Tree.exp
    val call: Temp.label * Types.ty list -> Tree.exp
    val arrayConst: Tree.exp* Tree.exp -> Tree.exp
    val recordConst: Tree.exp list * Symbol.symbol list  -> Tree.exp
    val seq: Tree.exp list -> Tree.exp
    val var: Symbol.symbol -> Tree.exp
    val recordVar: Symbol.symbol * Tree.exp -> Tree.exp
    val arrayVar: Tree.exp * Tree.exp -> Tree.exp
    
    
    val intConst: int -> Tree.exp
    val stringConst: string -> Tree.exp
    
    
end

structure Translate : TRANSLATE = 
struct
    structure F = Amd64Frame
    structure T = Temp
    structure Tr = Tree
    structure A = Absyn
    
    datatype level = Top | Level of {parent: level, name: T.label, formals: bool list, frame: F.frame}
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
        Level{parent = parent, name = name, formals = formals, frame = F.newFrame({name=name,formals=(true :: formals)})}
    
        
    fun formals(level as Level{parent, name, formals, frame}) =
    (
        case F.formals frame of [] => 
        (
            ErrorMsg.impossible "Frame has no formals"; 
            []
        )
        | _ :: formals => map (fn frameAccess => Access(level, frameAccess)) formals
    )
    | formals(Top) = []
    
    fun allocLocal (level as Level {parent, name, frame, formals}) escapes = Access(level, F.allocLocal frame escapes)
    | allocLocal Top _ = ErrorMsg.impossible "Can't alloc in top frame"
    
    
    fun opTree(A.PlusOp, left, right) = 
        Tr.BINOP(Tr.PLUS, left, right)
    | opTree(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    
    
    fun assign(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun ifElse(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun ifThen(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun whileTree(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun breakJump(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun call(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun intConst(integer) = 
        Tr.CONST(integer)
        
    fun stringConst(str) = ErrorMsg.impossible "UNIMPLEMENTED"
        
    fun arrayConst(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun recordConst(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun seq(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun var(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun recordVar(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    fun arrayVar(_) = ErrorMsg.impossible "UNIMPLEMENTED"
    
    
    
    
        
end
    
