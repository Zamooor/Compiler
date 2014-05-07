signature TRANSLATE = 
sig
    type level
    type access
    
    val outermost : level (*????*)
    val newLevel : {parent: level, name: label, formals: bool list} -> level
    val formals: level -> access list
    val allocLocal: level-> bool -> access
end

structure Translate : TRANSLATE = 
struct
    structure F = Frame
    structure T = Temp
    datatype level = Top | Level of {parent: level, name: T.label, formals: bool list, frame: F.frame}
    datatype access = level * Frame.access
    
    val outermostLevel = Top
    
    fun newLevel({parent, name, formals}) = 
        Level{parent = parent, name = name, formals = formals, frame = F.newFrame({name,formals})}
    | newLevel(parent=Top, name, formals) =
        Level{parent = Top, name = name, formals = formals, frame = F.newFrame({name,formals})}
        
    fun formals(level as Level{parent, name, formals, frame}) =
       map (fun conv(access) = (level, access)) F.formals(frame)
    | formals(Top) = {}
    
    fun allocLocal(level as Level{parent, name, formals, frame})=
        (level, F.allocLocal frame)
        
end
    
