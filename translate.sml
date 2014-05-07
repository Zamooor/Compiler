signature TRANSLATE = 
sig
    type level
    type access
    
    val outermost : level (*????*)
    val newLevel : {parent: level, name: Temp.label, formals: bool list} -> level
    val formals: level -> access list
    val allocLocal: level-> bool -> access
end

structure Translate : TRANSLATE = 
struct
    structure F = Amd64Frame
    structure T = Temp
    datatype level = Top | Level of {parent: level, name: T.label, formals: bool list, frame: F.frame}
    datatype access = Access of (level * F.access)
    
    val outermost = Top
    
    fun newLevel({parent, name, formals}) = 
        Level{parent = parent, name = name, formals = formals, frame = F.newFrame({name=name,formals=formals})}
    
        
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
        
end
    
