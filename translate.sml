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
    
    val procEntryExit : level * exp -> unit
    val getResult : unit -> Amd64Frame.frag list

    val opTree: Absyn.oper * exp * exp -> exp
    val assign: exp * exp -> exp
    val ifElse: exp * exp * exp -> exp
    val ifThen: exp * exp -> exp
    val whileTree: exp * exp * Temp.label -> exp
    val breakJump: Temp.label -> exp
    val call: Temp.label * exp list * level * level -> exp
    val arrayConst: exp* exp -> exp
    val recordConst: exp list * int -> exp
    val seq: Tree.stm list -> exp
    val expseq: exp list -> exp
    val simpleVar: access * level -> exp
    val recordVar: exp * exp -> exp
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
    
    val fragList = ref [] : Amd64Frame.frag list ref
    
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
    
    
    fun procEntryExit(Level {parent, name, frame, formals, unique}, body) =
    (
        fragList := !fragList @ [F.PROC{body=F.procEntryExit1(frame, Tr.SEQ(unNx(body), Tr.MOVE(Tr.TEMP(F.rax), unEx(body)))), frame=frame}];
        ()
    )
    | procEntryExit(TOP, _) = 
        ErrorMsg.impossible "NO! Can not enter top level!"
        
    fun getResult() = 
        !fragList
    
    fun seq [] = Nx(Tr.EXP (Tr.CONST 0))
    | seq [stm1] = Nx(stm1)
    | seq (stm :: stms) = Nx(Tr.SEQ (stm, unNx(seq stms)))
    

    fun expseq [] = Ex(Tr.CONST 0)
    | expseq [stm1] = stm1
    | expseq (stm :: stms) = Ex(Tr.ESEQ (unNx(stm), unEx(expseq stms)))

    fun opTree(A.PlusOp, left, right) =
        Ex(Tr.BINOP(Tr.PLUS, unEx(left), unEx(right)))
    | opTree(A.MinusOp, left, right) = 
        Ex(Tr.BINOP(Tr.MINUS, unEx(left), unEx(right)))
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
			seq[Tr.LABEL(testLab),
					(unCx(test) (bodyLab, breakLab)),
					Tr.LABEL(bodyLab),
					(unNx(body)),
					Tr.JUMP(Tr.NAME(testLab), [testLab]),
					Tr.LABEL(breakLab)]
		end
    
    fun breakJump(breakLab) =
		Nx(Tr.JUMP(Tr.NAME(breakLab), [breakLab]))
    


    fun intConst(integer) = 
        Ex(Tr.CONST(integer))
        
    fun stringConst(str) =
		let
			val strLab = T.newlabel()
		in
			Ex(Tr.NAME strLab)
		end
        
   
    fun islvlequal(Level{parent=_, name=_, formals=_, frame=_, unique=u1}, 
			Level{parent=_, name=_, formals=_, frame=_, unique=u2}) = (u1=u2)
	| islvlequal(_, _) = 
		ErrorMsg.impossible "Should never occure, variables can not be declared in Top"


    fun followstlink(deflevel, curlevel) = 
	(
	if(islvlequal(deflevel,curlevel))
	    then Tr.TEMP(F.rbp)
	else
		case 	curlevel
		of 	Level {parent, name, formals, frame, unique} => followstlink(deflevel,parent)
		|	Top => (ErrorMsg.impossible "following static link reached top level")
	)	

    fun call(funcLab, formals, funlevel, curlevel) =
	let
			val args = map unEx formals

	in
		case funlevel
			of Top => Ex(Tr.CALL(Tr.NAME(funcLab), args))
			  |Level {parent, name, formals, frame, unique} =>
				let 
					val args' = followstlink(parent,curlevel)::args
				in
					Ex(Tr.CALL(Tr.NAME(funcLab), args'))
				end
    	end

    fun simpleVar(Access(varlevel, access), uselevel) = 
		Ex( F.exp (access) (followstlink(varlevel,uselevel)) )

    (*fieldVar*)
    fun recordVar(varExp, indexExp) = 
		Ex(Tr.MEM (Tr.BINOP(Tr.PLUS, 
					 unEx(varExp), 
					 Tr.BINOP(Tr.MUL,
						  Tr.MEM(unEx(indexExp)),Tr.CONST(F.wordsize)
						 )
				   )
			 )
		  )	   

    
    (*subscriptVar*)
    fun arrayVar(varExp, indexExp) = 
	Ex(Tr.MEM(Tr.BINOP(Tr.PLUS, 
				Tr.MEM(unEx(varExp)), 
				Tr.BINOP(Tr.MUL,
					unEx(indexExp),Tree.CONST(F.wordsize)))))

 (*  
     fun arrayConst(sizeExp,initExp) = 
		let 
			val arraytemp = Tr.TEMP(T.newtemp())
		in
			Ex(Tr.ESEQ(Tr.SEQ(Tr.MOVE(arraytemp, F.externalCall("malloc", [Tr.BINOP(Tr.MUL, unEx(sizeExp), Tr.CONST(F.wordsize))])
						 ),
					   Tr.EXP (F.externalCall("initArray", [unEx(sizeExp), unEx(initExp)])
						  )
					),
				   arraytemp
				  )
			  )
		end
 *)
   fun arrayConst(sizeExp,initExp) = Ex(F.externalCall("initArray", [unEx(sizeExp), unEx(initExp)]))

    fun initField(fieldexp::tail, index) =
	let 
		
		val alloc = recordVar(fieldexp,intConst(index))
	in
		Tr.SEQ(Tr.MOVE(unEx(alloc), unEx(fieldexp)),
			initField(tail, index+1))
	end
	| initField(nil, index) = Tr.EXP (Tr.CONST 0)

    fun recordConst(fieldExps,count) = 
		let
			val recordtemp = Tr.TEMP(T.newtemp())
			val idx = 0

		in
			Ex(Tr.ESEQ(Tr.SEQ(Tr.MOVE (recordtemp, F.externalCall("allocRecord", [Tr.CONST(count * F.wordsize)])
					         ),
				 	  initField(fieldExps, 0)
					 ),
				   recordtemp
				  )
			  )
		end   
    
    
        
end
    
