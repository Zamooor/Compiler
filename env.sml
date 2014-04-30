signature ENV = 
sig
    datatype enventry = VarEntry of {ty: Types.ty}
                    | FunEntry of {formals: Types.ty list, result: Types.ty}
                    
    val base_tenv : Types.ty Symbol.table
    val base_venv : enventry Symbol.table
end

structure Env : ENV =
struct

    datatype enventry = VarEntry of {ty: Types.ty}
                    | FunEntry of {formals: Types.ty list, result: Types.ty}

    structure S = Symbol
    structure T = Types

    type venv = enventry S.table
    type tenv = Types.ty S.table 
    
    type access = T.ty (* no idea what this is for yet *)
    
    val basetypes = [("string", Types.STRING), 
                    ("int", Types.INT)]
    
    val basefunctions = [("print", FunEntry{formals=[T.STRING], result=T.UNIT}),
                        ("flush", FunEntry{formals=[], result=T.UNIT}),
                        ("getchar", FunEntry{formals=[], result=T.STRING}),
                        ("ord", FunEntry{formals=[T.STRING], result=T.INT}),
                        ("chr", FunEntry{formals=[T.INT], result=T.STRING}),
                        ("size", FunEntry{formals=[T.STRING], result=T.INT}),
                        ("substring", FunEntry{formals=[T.STRING, T.INT, T.INT], result=T.STRING}),
                        ("concat", FunEntry{formals=[T.STRING, T.STRING], result=T.STRING}),
                        ("not", FunEntry{formals=[T.INT], result=T.INT}),
                        ("exit", FunEntry{formals=[T.INT], result=T.UNIT})
                        ]

    fun enterTy((name, ty), tenv) = S.enter(tenv, S.symbol name, ty)
    val base_tenv = List.foldr enterTy S.empty basetypes
           
                        
    fun enterVar((name, enventry), venv) = S.enter (venv, S.symbol name, enventry)
    val base_venv = List.foldr enterVar S.empty basefunctions                  
    
end
