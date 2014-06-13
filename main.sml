structure Main = struct

   structure Tr = Translate
   structure F = Amd64Frame
   structure C = Canon

 fun getsome (SOME x) = x

   fun emitproc out (F.PROC{body,frame}) =
     let 
        val freeRegs = ref [F.rbx, F.r12, F.r13, F.r14, F.r15]
        val allocatedTemps = ref []
        fun allocTemp(t) = 
        (
            let
                val length = List.length(!freeRegs);
            in
                if length = 0 then
                    t
                else
                    case (List.exists (fn x => t=x) F.registerTemps) of true => t
                    | _ => 
                    (
                        
                        case  (List.find (fn ({tmp, reg}) => tmp = t) (!allocatedTemps)) of SOME {tmp, reg} => 
                            reg
                        | NONE =>
                            let
                                val reg = List.hd (!freeRegs)
                            in
                                freeRegs := List.tl (!freeRegs);
                                allocatedTemps := [{tmp=t, reg=reg}] @ (!allocatedTemps);
                                reg
                            end
                    )
            end
        )
        fun allocReg (Assem.OPER{assem, dst, src, jump=SOME jump}) = 
            let
               
                val dst' = map allocTemp dst
                val src' = map allocTemp src
            in
                Assem.OPER{assem=assem, dst=dst', src=src', jump=SOME jump}
            end
        | allocReg (Assem.OPER{assem, dst, src, jump=NONE}) = 
            let
                val dst' = map allocTemp dst
                val src' = map allocTemp src
            in
                Assem.OPER{assem=assem, dst=dst', src=src', jump=NONE}
            end
        | allocReg (label) = 
            label
        val _ = print ("emit " ^ Symbol.name(F.name frame) ^ "\n")
(*         val _ = Printtree.printtree(TextIO.stdOut,body) *)
	    val stms = Canon.linearize body
(*         val _ = app (fn s => Printtree.printtree(TextIO.stdOut,s)) stms *)
        val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	    val instrs =   List.concat(map (x64Gen.codegen frame) stms') 
	    val instrs' = map allocReg instrs
	    fun tempname t = 
	        case (Temp.Table.look(F.tempMap, t)) of 
	            SOME r => 
	                r
	            | NONE => "t" ^ Int.toString t
        val format0 = Assem.format(tempname)
      in
      ( 
        TextIO.output(out, "global L3\n");
        app (fn i => TextIO.output(out,format0 i)) instrs';  
        TextIO.output(out, "mov rdi, rax  \nmov eax, 60  \nsyscall  \n");      
        TextIO.output(TextIO.stdOut, "global L3\n");
        app (fn i => TextIO.output(TextIO.stdOut,format0 i)) instrs';
        TextIO.output(TextIO.stdOut, "mov rdi, rax  \nmov eax, 60  \nsyscall  \n")
      )

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
