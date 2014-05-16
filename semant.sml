structure Semant :
sig
    
    val transProg: Absyn.exp -> {exp : Translate.frag list, ty: Types.ty}
    
end
= 
struct

    structure S = Symbol
    structure T = Types
    structure A = Absyn
    structure E = Env
	structure Tr = Translate
	structure Te = Temp
    structure A = Absyn

    type expty = {exp: Translate.exp, ty: Types.ty}
    
	val currLevel = Tr.outermost
    
    fun checkInt ({exp, ty}, pos) = 
        case ty of Types.INT => ()
                | _ => ErrorMsg.error pos ("integer required, found a " ^ (T.toString ty))
                
	fun actual_ty (T.NAME (s, ty), pos) =
		(case !ty of
			NONE =>
			(
				ErrorMsg.error pos "Name type without actual type";
				T.UNIT
			)
		|	SOME t => actual_ty (t, pos))
	| actual_ty (t, pos) = t
                
    fun transExp(venv, tenv, exp, currLevel, breakLab) = 
        let 
            fun 
                (**** ARITHMETIC ****)
                
                trexp (A.OpExp{left, oper = A.PlusOp, right, pos}) = 
                (
                    (* fyi: checkInt was a bad idea!*)
                    (* Cause now I have to trexp a second time to get the exp of left/right...*)
                    (* -Jeff *)
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=Tr.opTree(A.PlusOp, #exp (trexp left), #exp (trexp right)),ty=T.INT}
                ) 
                | trexp (A.OpExp{left, oper = A.MinusOp, right, pos}) =
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=Tr.opTree(A.MinusOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )
                | trexp (A.OpExp{left, oper = A.TimesOp, right, pos}) =
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=Tr.opTree(A.TimesOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )
                | trexp (A.OpExp{left, oper = A.DivideOp, right, pos}) =
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=Tr.opTree(A.DivideOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )
                
                (**** COMPARISON ****)
                
                | trexp (A.OpExp{left, oper = A.EqOp, right, pos}) =
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left, currLevel, breakLab)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right, currLevel, breakLab)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        | T.ARRAY(typ, _) =>
						(
							case tyright of T.ARRAY(rtyp, _) =>
							(
								if (typ = rtyp) then
									()
								else
									ErrorMsg.error pos "Array types do not match"
							)
							| _ => ErrorMsg.error pos ("Cannot compare an array with a " ^ (T.toString tyright))
						)
                        | T.RECORD(fields, _) => 
                        (
                            case tyright of T.RECORD(rfields, _) =>
                                if fields = rfields then
                                    ()
                                else
                                    ErrorMsg.error pos "Records are not of the same type"
                            | _ => ErrorMsg.error pos "RVALUE is not of type record"
                        )
                        | T.STRING => 
                        (
                            case tyright of T.STRING => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found a STRING and a ____, expected a STRING and a STRING"
                        )
                        | _ =>
                        (
                            case tyright of T.INT => ErrorMsg.error pos "operator missmatch: found a ____ and an INT, expected an INT and an INT"
                            | T.STRING => ErrorMsg.error pos "operator mismatch: found a ____ and a STRING, expected a STRING and a STRING"
                            (*| T.ARRAY => ErrorMsg.error pos "operator mismatch: found a ____ and an ARRAY, expected an ARRAY and an ARRAY" *)
                            (*| T.RECORD => ErrorMsg.error pos "operator mismatch: found a ____ and a RECORD, expected a RECORD and a RECORD" *)
                            | _ => ErrorMsg.error pos "Expecting a pair of type INT, STRING, ARRAY, or RECORD"
                        )
                        
                    end;
                    {exp=Tr.opTree(A.EqOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )
                | trexp(A.OpExp{left, oper = A.NeqOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left, currLevel, breakLab)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right, currLevel, breakLab)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        | T.ARRAY(typ, _) =>
						(
							case tyright of T.ARRAY(rtyp, _) =>
							(
								if (typ = rtyp) then
									()
								else
									ErrorMsg.error pos "Array types do not match"
							)
							| _ => ErrorMsg.error pos ("Cannot compare an array with a " ^ (T.toString tyright))
						)
                        | T.RECORD(fields, _) => 
                        (
                            case tyright of T.RECORD(rfields, _) =>
                                if fields = rfields then
                                    ()
                                else
                                    ErrorMsg.error pos "Records are not of the same type"
                            | _ => ErrorMsg.error pos "RVALUE is not of type record"
                        )
                        | T.STRING => 
                        (
                            case tyright of T.STRING => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found a STRING and a ____, expected a STRING and a STRING"
                        )
                        | _ =>
                        (
                            case tyright of T.INT => ErrorMsg.error pos "operator missmatch: found a ____ and an INT, expected an INT and an INT"
                            | T.STRING => ErrorMsg.error pos "operator mismatch: found a ____ and a STRING, expected a STRING and a STRING"
                            (*| T.ARRAY => ErrorMsg.error pos "operator mismatch: found a ____ and an ARRAY, expected an ARRAY and an ARRAY" *)
                            (*| T.RECORD => ErrorMsg.error pos "operator mismatch: found a ____ and a RECORD, expected a RECORD and a RECORD" *)
                            | _ => ErrorMsg.error pos "Expecting a pair of type INT, STRING, ARRAY, or RECORD"
                        )
                        
                    end;
                    {exp=Tr.opTree(A.NeqOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )
                | trexp (A.OpExp{left, oper = A.GtOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left, currLevel, breakLab)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right, currLevel, breakLab)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        | T.STRING => 
                        (
                            case tyright of T.STRING => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found a STRING and a ____, expected a STRING and a STRING"
                        )
                        | _ =>
                        (
                            case tyright of T.INT => ErrorMsg.error pos "operator missmatch: found a ____ and an INT, expected an INT and an INT"
                            | T.STRING => ErrorMsg.error pos "operator mismatch: found a ____ and a STRING, expected a STRING and a STRING"
                            | _ => ErrorMsg.error pos "Expecting a pair of type INT, STRING, ARRAY, or RECORD"
                        )
                    end;
                    {exp=Tr.opTree(A.GtOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                ) 
                | trexp (A.OpExp{left, oper = A.LtOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left, currLevel, breakLab)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right, currLevel, breakLab)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        | T.STRING => 
                        (
                            case tyright of T.STRING => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found a STRING and a ____, expected a STRING and a STRING"
                        )
                        | _ =>
                        (
                            case tyright of T.INT => ErrorMsg.error pos "operator missmatch: found a ____ and an INT, expected an INT and an INT"
                            | T.STRING => ErrorMsg.error pos "operator mismatch: found a ____ and a STRING, expected a STRING and a STRING"
                            | _ => ErrorMsg.error pos "Expecting a pair of type INT, STRING, ARRAY, or RECORD"
                        )
                    end;
                    {exp=Tr.opTree(A.LtOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )    
                | trexp (A.OpExp{left, oper = A.GeOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left, currLevel, breakLab)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right, currLevel, breakLab)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        | T.STRING => 
                        (
                            case tyright of T.STRING => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found a STRING and a ____, expected a STRING and a STRING"
                        )
                        | _ =>
                        (
                            case tyright of T.INT => ErrorMsg.error pos "operator missmatch: found a ____ and an INT, expected an INT and an INT"
                            | T.STRING => ErrorMsg.error pos "operator mismatch: found a ____ and a STRING, expected a STRING and a STRING"
                            | _ => ErrorMsg.error pos "Expecting a pair of type INT, STRING, ARRAY, or RECORD"
                        )
                    end;
                    {exp=Tr.opTree(A.GeOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )          
                | trexp (A.OpExp{left, oper = A.LeOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left, currLevel, breakLab)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right, currLevel, breakLab)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        | T.STRING => 
                        (
                            case tyright of T.STRING => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found a STRING and a ____, expected a STRING and a STRING"
                        )
                        | _ =>
                        (
                            case tyright of T.INT => ErrorMsg.error pos "operator missmatch: found a ____ and an INT, expected an INT and an INT"
                            | T.STRING => ErrorMsg.error pos "operator mismatch: found a ____ and a STRING, expected a STRING and a STRING"
                            | _ => ErrorMsg.error pos "Expecting a pair of type INT, STRING, ARRAY, or RECORD"
                        )
                    end;
                    {exp=Tr.opTree(A.LeOp, #exp (trexp left), #exp (trexp right)), ty=T.INT}
                )   
                
                (**** ASSIGN ****)
                
                | trexp (A.AssignExp {var, exp, pos}) = 
                (
                    let 
				        val {exp=rexp,ty = rty} = transExp (venv, tenv, exp, currLevel, breakLab)
				        val {exp=lexp,ty=lty} = trvar(var)
	         		in
	         		    
	         		    if lty = rty then ()
	         		    else
	         		        ErrorMsg.error pos "lvalue and rvalue in assign didn't match";
         		        
         		        {exp=Tr.assign(rexp, lexp), ty=T.UNIT}
	         		    
				
			        end
			        
			        
		        )
                
                
                (**** IF and BOOL OPS ****)
                
                | trexp (A.IfExp{test, then', else' = SOME elseExp, pos}) =
                (                   
                    let
                        val {exp=expTest, ty=tytest} = transExp(venv, tenv, test, currLevel, breakLab)
                        val {exp=expThen, ty=tythen} = transExp(venv, tenv, then', currLevel, breakLab)
                        val {exp=expElse, ty=tyelse} = transExp(venv, tenv, elseExp, currLevel, breakLab)
                    in
                    (
                        case tytest of T.INT => ()                            
                        | _ => ErrorMsg.error pos "Expected to find an INT in the conditional";
                        
                        if(tythen = tyelse) then
                            {exp=Tr.ifElse(expTest, expThen, expElse), ty=tythen}
                        else
                        (
                            ErrorMsg.impossible "Branch types of if expression must match"
                        )  
                    )               
                    end                    
                )                
                | trexp (A.IfExp{test, then', else' = NONE, pos}) =
                (                   
                    let
                        val {exp=expTest, ty=tytest} = transExp(venv, tenv, test, currLevel, breakLab)
                        val {exp=expThen, ty=tythen} = transExp(venv, tenv, then', currLevel, breakLab)
                    in
                    (
                        case tytest of T.INT => ()
                        | _ => ErrorMsg.error pos "Expected to find an INT in the conditional";
                        
                        case tythen of T.UNIT => ()
                        | _ => ErrorMsg.error pos "Found no matching ELSE, expected the single branch to have no value"
                    );
                    
                        {exp=Tr.ifThen(expTest, expThen), ty=T.UNIT}                                
                    end             
                )
                
                (**** LOOPS ****)  
                
                | trexp (A.WhileExp{test, body, pos})=
                (
                    let
						val newBreakLab = SOME(Te.newlabel())
                        val {exp=expTest, ty=tytest} = transExp(venv, tenv, test, currLevel, newBreakLab)
                        val {exp=expBody, ty=tybody} = transExp(venv, tenv, body, currLevel, newBreakLab)
                    in
                    (
                        case tytest of T.INT => ()
                        | _ => ErrorMsg.error pos "Expected to find an INT in the conditional";
                        
                        case tybody of T.UNIT => ()
                        | _ => ErrorMsg.error pos "Body of loop must have no value"
                    );     
                    
                    {exp=Tr.whileTree(expTest, expBody, valOf(newBreakLab)), ty=T.UNIT}                           
                    end  
                ) 
                
                | trexp (A.ForExp{var,escape, lo, hi, body, pos})=
                (
                    let
						val newBreakLab = SOME(Te.newlabel())
                        val {exp=expLo, ty=tylo} = transExp(venv, tenv, lo, currLevel, breakLab)
                        val {exp=expHi, ty=tyhi} = transExp(venv, tenv, hi, currLevel, breakLab)
                        
                        val access = Tr.allocLocal(currLevel)(!escape)
                        val venv' = S.enter(venv, var, E.VarEntry{ty=T.INT})
                        val {exp=expBody, ty=tybody} = transExp(venv', tenv, body, currLevel, newBreakLab)
                    in
                    (
                        
                        
                        case tylo of T.INT => ()
                        | _ => ErrorMsg.error pos "lower bound of loop must be an integer";
                        
                        case tyhi of T.INT => ()
                        | _ => ErrorMsg.error pos "higher bound of loop must be an integer";
                        
                        case tybody of T.UNIT => ()
                        | _ => ErrorMsg.error pos "Body of loop must have no value"
                    );
                    (* first attempt please help *)
                    (*{exp=transExp(venv, tenv, A.LetExp({[A.VarDec{var, True, SOME tylo, lo, pos}, A.VarDec{S.symbol('limit'), True, SOME tyhi, hi, pos}], A.WhileExp{A.OpExp{lo, A.LeOp, hi}, A.SeqExp([(body, pos), (IfExp({A.OpExp{ , ty=T.UNIT}   *)
                    
                    {exp=(#exp (transExp(venv, tenv, A.OpExp{left=lo, oper=A.PlusOp, right=hi, pos = pos}, currLevel, newBreakLab))), ty = T.UNIT}
					end
                )  
                
                | trexp (A.BreakExp pos) = (
					case breakLab of
						NONE => (
							ErrorMsg.error pos "You cannot break here!";
							{exp=Tr.breakJump(Temp.newlabel()) , ty = T.UNIT}    
						)
					|	SOME(bLab) => {exp = Tr.breakJump(bLab), ty = T.UNIT}
				)
                
                (**** FUNCTION CALL ****)
                
                | trexp (A.CallExp{func, args, pos}) = 
                (
                    case S.look(venv, func) of SOME(E.FunEntry{formals, result, level, label}) =>
                    (
                        let 
                            val argtypes = map #ty (map (fn x => transExp(venv, tenv, x, currLevel, breakLab)) args)
                        in   
                        (
                            if argtypes = formals then
                                ()
                            else
                                ErrorMsg.error pos ("function call doesn't match the signature of "^S.name(func));
                            (* maybe have to add extra formal for static link? *)
                            {exp = Tr.call(label, formals), ty = result}
                        )
                        end
                    )
                    | _ => 
                    (
                        ErrorMsg.impossible (S.name(func)^" is not a function")
                    )
                )
                
                (**** LITERALS ****) 
				| trexp (A.NilExp) = {exp = Tr.intConst(0), ty=Types.NIL}
				| trexp (A.StringExp (s, p)) = {exp = Tr.stringConst(s), ty = Types.STRING}
                | trexp (A.IntExp int) = 
                (
                    {exp=Tr.intConst(int),ty=Types.INT}
                )
				| trexp (A.ArrayExp {typ, size, init, pos}) =
				let
				    (* again checkInt making me do silly redundant things... *)
				    val {exp=expSize, ty=tySize} = transExp(venv, tenv, size, currLevel, breakLab)
			        val {exp=expInit, ty=tyInit} = transExp(venv, tenv, init, currLevel, breakLab)
					val sizeTr = trexp size
					val initTr = trexp init
				in
				(
					checkInt(sizeTr, pos);
					case S.look(tenv, typ) of
						SOME (realAryType as T.ARRAY (ty, _)) =>
						(
							actual_ty (ty, pos);
							{exp = Tr.arrayConst(expSize, expInit), ty = realAryType}
						)
					|	NONE =>
						(
							ErrorMsg.error pos ("Type is not defined: " ^ S.name typ);
							{exp = Tr.arrayConst(expSize, expInit), ty = T.UNIT}
						)
					|	_ =>
						(
							ErrorMsg.error pos "Type is not of array type";
							{exp = Tr.arrayConst(expSize, expInit), ty = T.UNIT}
						)
				)
				end
                | trexp(A.RecordExp {fields, typ, pos}) =
                (
                    let
                        fun transFields (symbol, exp, pos) =
                        (
                            let
                                val {exp=expField,ty = rty} = transExp (venv, tenv, exp, currLevel, breakLab)
		                    in
		                    (
			                   
     		                    ((symbol, rty), expField)
     		                )
     		                end
 		                )
                        val tfields = map (transFields) (fields)
                    in
                        {exp=Tr.recordConst(map #2 tfields, map #1 (map #1 tfields)),ty=T.RECORD( map #1 tfields,ref())}              
                    end
                )
                
                (**** LET ****)
    
		        | trexp(A.LetExp{decs,body,pos}) = 
			        let 
				        val {venv=venv',tenv=tenv'} = transDec(venv,tenv,decs, currLevel, breakLab)
			        in
				        transExp(venv',tenv',body, currLevel, breakLab)
			        end
                
                (**** SEQ ****)

		        | trexp (A.SeqExp expList) =
		        (
			        if (length (expList) = 0) then
				        {exp = Tr.seq([]), ty = T.UNIT}
			        else
			            List.last(map (fn x => transExp(venv, tenv, #1 x, currLevel, breakLab)) expList)
				
		        )
		        
	        	(**** VARIABLE EXPRESSIONS ****)
                | trexp (A.VarExp var) = trvar var
		     
	            (**** TRANSLATING ALL TYPES OF VARS ****)
                and trvar (A.SimpleVar (id, pos)) =
		        (
			        case S.look(venv, id) of
				        SOME(E.VarEntry{ty}) => {exp = Tr.var(id), ty = actual_ty (ty, pos)}
			        |	NONE =>
			        (
				        ErrorMsg.error pos ("undefined variable " ^ S.name id);
				        {exp = Tr.var(id), ty = T.UNIT}
			        )
			        | _ =>
			        (
				        ErrorMsg.error pos ("Something broke while looking up a var entry");
				        {exp = Tr.var(id), ty = T.UNIT}
			        )
		        )
		        | trvar (A.FieldVar(v, id, pos)) =
		        (
		            let
		                val {exp, ty} = trvar(v)
		                fun findField((field, typ), NONE) =
						            (if id = field then SOME(typ) else NONE)
					            |	findField(_, fMatch as SOME(typ)) = fMatch
	                in
			            case ty of T.RECORD(fields, _)  =>
		                (
				            case (foldl findField NONE fields) of
						            SOME(typ) => {exp = Tr.recordVar(id, exp), ty = typ}
				            |	NONE => 
				            (
					            ErrorMsg.impossible ("Field " ^ S.name(id) ^ " does not exist")
				            )
			            )
			            |	_ =>
				        (
					        ErrorMsg.impossible "Record doesn't exist"
				        )
		            end
			        
		        )
		        | trvar (A.SubscriptVar(v, ex, pos)) =
		            let
			            val {exp = indExp, ty = expTy} = (trexp ex)
		            in
			            checkInt ((trexp ex), pos);
			            case trvar v of
				            {exp = varExp, ty = T.ARRAY(typ, _)} => {exp = Tr.arrayVar(indExp, varExp), ty = typ}
			            |	{exp, ty} =>
			            (
				            ErrorMsg.impossible "Variable is not an array"
			            )
		            end
        in 
            trexp(exp)
        end
    

    and transTy (tenv, A.NameTy(name,_),pos) = 
		(case Symbol.look (tenv, name) of
       			NONE => T.NAME(name, ref NONE)
    			 | SOME ty => ty)
	|transTy(tenv, A.RecordTy(flist),pos) = 
		Types.RECORD ((map (fn {name, escape=_, typ, pos=pos'} =>
                       (name, (transTy (tenv, A.NameTy (typ, pos'), pos)))) flist),
              		ref())
	|transTy(tenv, A.ArrayTy(sym, pos'), pos) =
		Types.ARRAY (transTy (tenv, A.NameTy (sym, pos'), pos), ref ())

    and transDec (venv, tenv, decs, currLevel, breakLab) = 
	let
	    fun
		trdec (A.VarDec{name, escape,typ=NONE,init,pos}, venv', tenv') =
		(
			let 
				val {exp,ty} = transExp (venv', tenv', init, currLevel, breakLab)
				val access = Tr.allocLocal(currLevel)(!escape)
	 		in 
				{venv = S.enter(venv', name, E.VarEntry{ty=ty}), tenv = tenv'}
			end
		)
		| trdec (A.VarDec{name, escape,typ=SOME typ,init,pos}, venv', tenv') =
		(
		    
			let 
				val {exp,ty} = transExp (venv', tenv', init, currLevel, breakLab)
				val actty = actual_ty(getOpt(S.look(tenv', #1 typ), T.UNIT), pos)
				val access = Tr.allocLocal(currLevel)(!escape)
	 		in
 		    (
 		        case actty of T.RECORD(rfields,_)=>
	            (
 		            case ty of T.RECORD(lfields,_)=>
 		                if rfields = lfields then
 		                    ({venv = S.enter(venv', name, E.VarEntry{ty=ty}), tenv = tenv'})
                        else
                        (
                            ErrorMsg.error pos "Record types don't match";
                            {venv = venv', tenv = tenv'}
                        )
                    |_ =>
                    (
                        ErrorMsg.error pos("Can not ititalize a record as a "^T.toString(ty));
                        {venv = venv', tenv = tenv'}
                    )
                )
                | _ => 
                (
	     		    if actty = ty then
	     		        ({venv = S.enter(venv', name, E.VarEntry{ty=ty}), tenv = tenv'})
	     		    else
	     		    (
	     		        ErrorMsg.error pos("Could not initialize a "^T.toString(actty)^" to be a "^T.toString(ty)^"\n");
	     		        {venv = venv', tenv = tenv'}
     		        )
 		        )
			)
			end
		)
		|trdec(A.TypeDec tyDecList, venv', tenv') =
        (
            let

                fun addType ({name, ty, pos}, venv'', tenv'') =
                    {venv=venv'',tenv=S.enter(tenv'',name,transTy(tenv'',ty,ref ()))}

                and updateTypes (tdec, {venv = venv', tenv = tenv'}) = 
                (
                    addType (tdec, venv', tenv')
                )

            in
                foldl updateTypes {venv = venv', tenv = tenv'} tyDecList
            end
        )
		
		| trdec(A.FunctionDec funDecs, venv', tenv') =
			let 				
				fun transparam({name:S.symbol, escape:bool ref,typ:S.symbol,pos:A.pos}) =
				    let
				        val ty = actual_ty(getOpt(S.look(tenv',  typ), T.UNIT), pos)
				        val access = Tr.allocLocal(currLevel)(!escape)
			        in
					    case ty of T.UNIT =>
					    (
					        ErrorMsg.impossible ("type "^S.name(typ)^" is undefined");
					        {name=name, ty = T.UNIT}
				        )
				        | _ => {name=name, ty=ty}
					    
					end
				    
			    fun enterparam ({name,ty}, venv) = 
			        S.enter(venv, name, E.VarEntry{ty=ty})
			        

				fun transFun(fundec as {name, params, body, pos, result=SOME(rt,rpos)}, {venv, tenv}) =
					let 
					    val SOME(result_ty) = S.look(tenv, rt)
					    val params' = map transparam params
					    val label = Te.newlabel()
					    val formals = map ! (map #escape params)
					    val venv' = S.enter(venv, name, E.FunEntry{formals = map #ty params', result = result_ty, level = Tr.newLevel({parent=currLevel, name=label, formals=formals}),  label=label})
					    val venv'' = foldl enterparam venv' params' 
					    val rtype = actual_ty(getOpt(S.look(tenv,  rt), T.UNIT), pos)
					    val {exp=bexp, ty = btype} = transExp(venv'', tenv, body, currLevel, breakLab)
				    in
				        transExp(venv'', tenv, body, currLevel, breakLab);
				        if rtype = btype then
				            ()
			            else
			                ErrorMsg.error pos "the function does not return the value declared";
				        {venv=venv', tenv=tenv}
			        end
		        | transFun(fundec as {name, params, body, pos, result=NONE}, {venv, tenv}) = 
		            let
		                val params' = map transparam params
		                val label = Te.newlabel()
		                val formals = map ! (map #escape params)
					    val venv' = S.enter(venv, name, E.FunEntry{formals = map #ty params', result = T.UNIT, level = Tr.newLevel({parent=currLevel, name=label, formals=formals}),  label=label})
					    val venv'' = foldl enterparam venv' params' 
					    val rtype = T.UNIT
					    val {exp=bexp, ty=btype} = transExp(venv'', tenv, body, currLevel, breakLab)
				    in
				        transExp(venv'', tenv, body, currLevel, breakLab);
				        if rtype = btype then
				            ()
			            else
			                ErrorMsg.error pos "A procedure must return no value";
				        {venv=venv', tenv=tenv}
			        end
					
					
			in
				foldl transFun {venv = venv', tenv = tenv'} funDecs
			end
		
		
		and updateScope (dec, {venv, tenv}) = (
			(trdec (dec, venv, tenv))
		)
			
	in
		foldr updateScope {venv = venv, tenv = tenv} decs
	end
	and transProg(exp: A.exp) = 
		let
			val currLevel = Tr.newLevel({parent = Tr.outermost, name = Temp.namedlabel("tiger_main"), formals = []} )
			val {exp, ty} = transExp(Env.base_venv, Env.base_tenv, exp, currLevel, NONE);
		in
		    currLevel = Tr.newLevel({parent = currLevel, name = Temp.namedlabel("tiger_main"), formals = []} );
			{exp = [], ty = ty} (* this is stupid but I think is has to do with defining procedures... *)
		end
end
