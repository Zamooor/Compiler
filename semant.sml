structure Semant :
sig
    
    val transProg: Absyn.exp -> unit
    
end
= 
struct

    structure S = Symbol
    structure T = Types
    structure A = Absyn
	structure E = Env
    
    structure Translate = struct type exp = unit end

    type expty = {exp: Translate.exp, ty: Types.ty}
    
    structure A = Absyn
    
    fun checkInt ({exp, ty}, pos) = 
        case ty of Types.INT => ()
                | _ => ErrorMsg.error pos "integer required, found a " (* A way to print the type here would be great!*)
                
	fun actual_ty (Types.NAME (s, ty), pos) =
		(case !ty of
			NONE =>
			(
				ErrorMsg.error pos "Name type without actual type";
				T.UNIT
			)
		|	SOME t => actual_ty (t, pos))
	| actual_ty (t, pos) = t
                
    fun transExp(venv, tenv, exp) = 
        let 
            fun 
            
                (**** ARITHMETIC ****)
                
                trexp (A.OpExp{left, oper = A.PlusOp, right, pos}) = 
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=(),ty=T.INT}
                ) 
                | trexp (A.OpExp{left, oper = A.MinusOp, right, pos}) =
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=(), ty=T.INT}
                )
                | trexp (A.OpExp{left, oper = A.TimesOp, right, pos}) =
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=(), ty=T.INT}
                )
                | trexp (A.OpExp{left, oper = A.DivideOp, right, pos}) =
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=(), ty=T.INT}
                )
                
                (**** COMPARISON ****)
                
                | trexp (A.OpExp{left, oper = A.EqOp, right, pos}) =
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        (*| T.ARRAY => ((*check and see if the two array types match*)) *)
                        (*| T.RECORD => ((*check and see if the record types match*)) *)
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
                    {exp=(), ty=T.INT}
                )
                | trexp(A.OpExp{left, oper = A.NeqOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right)
                    in
                        case tyleft of T.INT =>
                        (
                            case tyright of T.INT => ()
                            | _ => ErrorMsg.error pos "operator mismatch: found an INT and a ____, expected an INT and a INT"
                        )
                        (*| T.ARRAY => ((*check and see if the two array types match*)) *)
                        (*| T.RECORD => ((*check and see if the record types match*)) *)
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
                    {exp=(), ty=T.INT}
                )
                | trexp (A.OpExp{left, oper = A.GtOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right)
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
                    {exp=(), ty=T.INT}
                ) 
                | trexp (A.OpExp{left, oper = A.LtOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right)
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
                    {exp=(), ty=T.INT}
                )    
                | trexp (A.OpExp{left, oper = A.GeOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right)
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
                    {exp=(), ty=T.INT}
                )          
                | trexp (A.OpExp{left, oper = A.LeOp, right, pos})=
                (
                    let
                        val {exp=_, ty=tyleft} = transExp(venv, tenv, left)
                        val {exp=_, ty=tyright} = transExp(venv, tenv, right)
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
                    {exp=(), ty=T.INT}
                )   
                
                (**** IF and BOOL OPS ****) (*TO DO: everything*)
                
                (**** LITERALS ****) (*TO DO: STRINGS*)
				| trexp (A.NilExp) = {exp = (), ty=Types.NIL}
				| trexp (A.StringExp (s, p)) = {exp = (), ty = Types.STRING}
                | trexp (A.IntExp int) = 
                (
                    {exp=(),ty=Types.INT}
                )
            (*    | trexp (A.recordExp ...) ...  *)
				| trexp (A.LetExp {decs, body, pos}) =
				(
					transExp(venv, tenv, body)
				)
				| trexp (A.SeqExp expList) =
				(
					if (length (expList) = 0) then
						{exp = (), ty = T.UNIT}
					else
						transExp(venv, tenv, (#1 (List.last expList)))
				)
				(**** VARIABLE EXPRESSIONS ****)
				| trexp (A.VarExp var) = (print "TRACE TRACE TRACE\n\n\n"; trvar var)
                | trexp _ =
                (
                    {exp=(), ty=T.NIL}
                ) 
				(**** TRANSLATING ALL TYPES OF VARS ****)
            and trvar (A.SimpleVar (id, pos)) =
				(
					case S.look(venv, id) of
						SOME(E.VarEntry{ty}) => {exp = (), ty = actual_ty (ty, pos)}
					|	NONE =>
					(
						ErrorMsg.error pos ("undefined variable " ^ S.name id);
						{exp = (), ty = Types.INT}
					)
					| _ =>
					(
						ErrorMsg.error pos ("Something broke while looking up a var entry");
						{exp = (), ty = Types.INT}
					)
				)
				| trvar _ =
				(
					{exp = (), ty = T.UNIT}
				)
				
        in 
            trexp(exp)
        end
    and transProg(exp: A.exp):unit = 
        (transExp(Env.base_venv, Env.base_tenv, exp);
        ()) (* this is stupid but I think is has to do with defining procedures... *)
end
    
    
