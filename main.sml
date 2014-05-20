structure Main = struct
structure Tr = Translate
structure F = Amd64Frame

fun compile filename = 
	let val absyn = Parse.parse filename
		val frags = #frags (Semant.transProg absyn)
		fun printProc (F.PROC{body = bod, frame = frm}) =
			Printtree.printtree(TextIO.stdOut, bod)
		|	printProc (F.STRING(lab, s)) =
				TextIO.output(TextIO.stdOut, s)
        in 
			app printProc frags;
       end
end
