structure Main = struct

   structure Tr = Translate

 fun compile filename = 
       let val absyn = Parse.parse filename
           val frags = (Semant.transProg absyn)
        in 
			PrintAbsyn.print(TextIO.stdOut , absyn)
       end

end
