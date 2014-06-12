signature FRAME =
sig
	type frame
	type access

	type register = string
	datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string

	val wordsize : int
	val rax : Temp.temp
	val rbp : Temp.temp
	
	val rdi : Temp.temp
	val rsi : Temp.temp
	val rdx : Temp.temp
	val rcx : Temp.temp
	val r8  : Temp.temp
	val r9  : Temp.temp

	val argregs : Temp.temp list
	val calleesaves : Temp.temp list
	val callersaves : Temp.temp list
	val specialregs : Temp.temp list
	val colorable : Temp.temp list
	val tempMap : register Temp.Table.table
	val registers : register list

	val newFrame : {name: Temp.label, formals: bool list} -> frame
	val name : frame -> Temp.label
	val formals : frame -> access list
	val allocLocal : frame -> bool -> access
	val exp : access -> Tree.exp -> Tree.exp
	val string : (Temp.label * string) -> string
	val externalCall : (string * Tree.exp list) -> Tree.exp
	val procEntryExit1 : (frame * Tree.stm) -> Tree.stm
	val procEntryExit2 : (frame * Assem.instr list) -> Assem.instr list
	val procEntryExit3 : (frame * Assem.instr list) -> {prolog : string,
														body : Assem.instr list,
														epilog : string}
end
