structure Main = struct

   structure Tr = Translate
   structure F = Amd64Frame
   structure C = Canon

 fun getsome (SOME x) = x

   fun emitproc out (F.PROC{body,frame}) =
     let 
        val _ = print ("emit " ^ Symbol.name(F.name frame) ^ "\n")
(*         val _ = Printtree.printtree(TextIO.stdOut,body) *)
	    val stms = Canon.linearize body
(*         val _ = app (fn s => Printtree.printtree(TextIO.stdOut,s)) stms *)
        val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	    val instrs =   List.concat(map (x64Gen.codegen frame) stms') 
	    fun tempname t = 
	        case (Temp.Table.look(F.tempMap, t)) of 
	            SOME r => 
	                r
	            | NONE => "t" ^ Int.toString t
        val format0 = Assem.format(tempname)
      in  
        app (fn i => TextIO.output(TextIO.stdOut,format0 i)) instrs

      end
    | emitproc out (F.STRING(lab,s)) = TextIO.output(out,F.string(lab,s))

   fun withOpenFile fname f = 
       let val out = TextIO.openOut fname
        in (f out before TextIO.closeOut out) 
	    handle e => (TextIO.closeOut out; raise e)
       end 

   fun compile filename = 
       let 
            val absyn = Parse.parse filename
           val frags = #frags (Semant.transProg absyn)
           fun printProc (F.PROC{body = bod, frame = frm}) =
			    Printtree.printtree(TextIO.stdOut, bod)
		    |printProc (F.STRING(lab, s)) =
			    TextIO.output(TextIO.stdOut, s)
		    fun printStm(bod) =			
			    Printtree.printtree(TextIO.stdOut, bod)
		    fun canonProc (F.PROC{body = bod, frame = frm}) =
		    (
	        	let
			        val canonBod = C.traceSchedule(C.basicBlocks(C.linearize(bod)));
	            in
				    app printStm canonBod
            	end
		    )
        in 
            app printProc frags;
            TextIO.output(TextIO.stdOut, "/*********************************/\n\tCanonized tree\n/*********************************/\n");
		    app canonProc frags;
		    TextIO.output(TextIO.stdOut, "/*********************************/\n\tASSEMBLY???\n/*********************************/\n");
            withOpenFile (filename ^ ".s") 
	     (fn out => (app (emitproc out) frags))
       end

end
