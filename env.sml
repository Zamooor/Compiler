signature ENV = 
sig
    datatype enventry = VarEntry of {ty: Types.ty, access: Translate.access}
                    | FunEntry of {formals: Types.ty list, result: Types.ty, level: Translate.level, label: Temp.label}
                    
    val base_tenv : Types.ty Symbol.table
    val base_venv : enventry Symbol.table
end

structure Env : ENV =
struct

    datatype enventry = VarEntry of {ty: Types.ty, access: Translate.access}
                    | FunEntry of {formals: Types.ty list, result: Types.ty, level: Translate.level, label: Temp.label}

    structure S = Symbol
    structure T = Types
    structure Tr = Translate
    structure Te = Temp

    type venv = enventry S.table
    type tenv = Types.ty S.table 
    
    
    val basetypes = [("string", Types.STRING), 
                    ("int", Types.INT)]
    
    val basefunctions = [("print", FunEntry{formals=[T.STRING], result=T.UNIT, level = Tr.outermost, label = Te.namedlabel("print")}),
                        ("flush", FunEntry{formals=[], result=T.UNIT, level = Tr.outermost, label = Te.namedlabel("flush")}),
                        ("getchar", FunEntry{formals=[], result=T.STRING, level = Tr.outermost, label = Te.namedlabel("getchar")}),
                        ("ord", FunEntry{formals=[T.STRING], result=T.INT, level = Tr.outermost, label = Te.namedlabel("ord")}),
                        ("chr", FunEntry{formals=[T.INT], result=T.STRING, level = Tr.outermost, label = Te.namedlabel("chr")}),
                        ("size", FunEntry{formals=[T.STRING], result=T.INT, level = Tr.outermost, label = Te.namedlabel("size")}),
                        ("substring", FunEntry{formals=[T.STRING, T.INT, T.INT], result=T.STRING, level = Tr.outermost, label = Te.namedlabel("substring")}),
                        ("concat", FunEntry{formals=[T.STRING, T.STRING], result=T.STRING, level = Tr.outermost, label = Te.namedlabel("concat")}),
                        ("not", FunEntry{formals=[T.INT], result=T.INT, level = Tr.outermost, label = Te.namedlabel("not")}),
                        ("exit", FunEntry{formals=[T.INT], result=T.UNIT, level = Tr.outermost, label = Te.namedlabel("exit")})
                        ]

    fun enterTy((name, ty), tenv) = S.enter(tenv, S.symbol name, ty)
    val base_tenv = List.foldr enterTy S.empty basetypes
           
                        
    fun enterVar((name, enventry), venv) = S.enter (venv, S.symbol name, enventry)
    val base_venv = List.foldr enterVar S.empty basefunctions                  
    
end
