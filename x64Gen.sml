structure x64Gen : CODEGEN = 
struct
    structure A = Assem 
    structure Frame = Amd64Frame
    structure T = Tree

    fun codegen (frame) (stm: Tree.stm) : Assem.instr list =
        let
            val ilist = ref (nil: A.instr list)
			fun emit x = ilist := x :: !ilist
			fun result(gen) = 
				let 
					val t = Temp.newtemp() 
				in 
					gen t; 
					t 
				end
	
	        fun getRelOp(relop) = 
	            case relop of 
	                T.EQ => "je"
                    | T.NE => "jne"
                    | T.LT => "jl"
                    | T.LE => "jle"
                    | T.GT => "jg"
                    | T.GE => "jge"
	
	        (* I don`t think this first pattern should happen, 
            all seq should be removed by canon step, 
            why is this in the book? *)
			fun munchStm(T.SEQ(a,b)) = 
			(
			    munchStm a;
			    munchStm b
		    )
		    | munchStm(T.EXP(e)) = 
	        (
		        munchExp(e);
		        ()
	        )
		    | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1)), e2)) = 
		        emit(A.OPER{assem="mov [`s0+" ^ Int.toString i ^ "], `s1\n",
		                    dst=[],
                            src=[munchExp e1, munchExp e2],
                            jump=NONE})
            | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) = 
		        emit(A.OPER{assem="mov [`s0+" ^ Int.toString i ^ "], `s1\n",
		                    dst=[],
                            src=[munchExp e1, munchExp e2],
                            jump=NONE})
            | munchStm(T.MOVE(T.MEM(T.CONST i), e1)) = 
		        emit(A.OPER{assem="mov [" ^ Int.toString i ^ "], `s0\n",
		                    dst=[],
                            src=[munchExp e1],
                            jump=NONE})
            | munchStm(T.MOVE(T.MEM(e1), e2)) = 
		        emit(A.OPER{assem="mov [`s0], `s1\n",
		                    dst=[],
                            src=[munchExp e1, munchExp e2],
                            jump=NONE})
            (* not in the drawing *)
            | munchStm(T.MOVE(T.TEMP i, e1)) = 
                emit(A.OPER{assem="add `d0, `s0\n",
                            dst=[i],
                            src=[munchExp e1],
                            jump=NONE})
            | munchStm(T.LABEL lab) =
                emit(A.LABEL{assem= Symbol.name(lab) ^ ":\n", lab=lab})
            (* (*Call may be very complicated, so I`m going to continue doing the easy stuff
                and come back to it later.*)
            | munchStm(T.EXP(T.CALL(e, args))) = 
                emit(
            *)
            | munchStm(T.JUMP(T.NAME n1, _)) =
                emit(A.OPER{assem="jmp `j0\n",
                            dst=[],
                            src=[],
                            jump=SOME [n1]})
            | munchStm(T.CJUMP(relop, e1, e2, l1, l2)) = 
                emit(A.OPER{assem="cmp `s0, `s1\n"^getRelOp(relop)^" `j0\njmp `j1\n",
                            dst=[],
                            src=[munchExp e1, munchExp e2],
                            jump= SOME [l1, l2]})
            (* Is there more munchStm to do???? *)
            | munchStm(_) = ErrorMsg.impossible "UHOH! We have found a pattern in the tree that isn`t implemented in munchStm!"
                        
            and munchExp(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i))) = 
                result(fn r => emit(A.OPER{assem="mov `d0, [`s0+" ^ Int.toString i ^ "]\n",
                                        dst=[r],
                                        src=[munchExp e1], 
                                        jump=NONE}))
            | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1))) = 
                result(fn r => emit(A.OPER{assem="mov `d0, [`s0+" ^ Int.toString i ^ "]\n",
                                        dst=[r],
                                        src=[munchExp e1], 
                                        jump=NONE}))
            | munchExp(T.MEM(T.CONST i)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, [" ^ Int.toString i ^ "]\n",
                                        dst=[r],
                                        src=[], 
                                        jump=NONE}))
            | munchExp(T.MEM(e1)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, [`s0]\n",
                                        dst=[r],
                                        src=[munchExp e1], 
                                        jump=NONE}))
            | munchExp(T.BINOP(T.PLUS,e1,T.CONST i)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, `s0\nadd `d0," ^ Int.toString i ^ "\n",
                                        dst=[r],
                                        src=[munchExp e1], 
                                        jump=NONE}))
            | munchExp(T.BINOP(T.PLUS,T.CONST i, e1)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, `s0\nadd `d0," ^ Int.toString i ^ "\n",
                                        dst=[r],
                                        src=[munchExp e1], 
                                        jump=NONE}))
            | munchExp(T.BINOP(T.PLUS,e1,e2)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, `s0\nadd `d0, `s1\n",
                                        dst=[r],
                                        src=[munchExp e1, munchExp e2], 
                                        jump=NONE}))
            | munchExp(T.CONST i) = 
                result(fn r => emit(A.OPER{assem="mov `d0," ^ Int.toString i ^ "\n",
                                        dst=[r],
                                        src=[], 
                                        jump=NONE}))            
            | munchExp(T.BINOP(T.MINUS,e1,e2)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, `s0\nsub `d0, `s1\n",
                                        dst=[r],
                                        src=[munchExp e1, munchExp e2], 
                                        jump=NONE}))
            | munchExp(T.BINOP(T.MUL,e1,e2)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, `s0\nmul `d0, `s1\n",
                                        dst=[r],
                                        src=[munchExp e1, munchExp e2], 
                                        jump=NONE}))
            | munchExp(T.BINOP(T.DIV,e1,e2)) = 
                result(fn r => emit(A.OPER{assem="mov `d0, `s0\ndiv `d0, `s1\n",
                                        dst=[r],
                                        src=[munchExp e1, munchExp e2], 
                                        jump=NONE}))
            | munchExp(T.TEMP t) = t
            
            (* if you look closely you will see that we are missing many things *)
            
            | munchExp(_) = ErrorMsg.impossible "UHOH! We have found a pattern in the tree that isn`t implemented in munchStm!"
            

		in
		    munchStm stm;
			rev(!ilist)
		end

end
