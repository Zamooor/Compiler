structure Semant :
sig
    
    val transProg: Absyn.exp -> unit
    
end
= 
struct

    structure S = Symbol
    structure T = Types
    structure A = Absyn
    
    structure Translate = struct type exp = unit end

    type expty = {exp: Translate.exp, ty: Types.ty}
    
    structure A = Absyn
    
    fun checkInt ({exp, ty}, pos) = 
        case ty of Types.INT => ()
                | _ => ErrorMsg.error pos "integer required"
                
    
                
    fun transExp(venv, tenv, exp) = 
        let 
            fun 
                trexp (A.OpExp{left, oper = A.PlusOp, right, pos}) = 
                (
                    checkInt(trexp left, pos);
                    checkInt(trexp right, pos);
                    {exp=(),ty=Types.INT}
                )    
            (*    | trexp (A.recordExp ...) ...  *)
                | trexp _ =
                (
                    
                    {exp=(), ty=T.NIL}
                ) 
            
            
        in 
            trexp(exp)
        end
    and transProg(exp: A.exp):unit = 
        (transExp(Env.base_venv, Env.base_tenv, exp);
        ()) (* this is stupid but I think is has to do with defining procedures... *)
end
    
    
