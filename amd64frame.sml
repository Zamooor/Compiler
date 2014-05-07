structure Amd64Frame : FRAME =
struct
(* NOTE that we a making the second paraeter to frame, the list of booleans always be TRUE,
 which means that everything escapes.
This is somewhat wasteful as a non-escaping variable doesn't need to be stored in memory and could 
just be used in the register. We don't care about the wasted space and are making this simplifying assumption
in order to not need to implement the findescapes routine and allocate things differently depending on 
whether they escape or not.
*)
  type frame = {name: Temp.label, formals: bool list, locals: int ref}
  type register = string
  datatype access = InFrame of int (* a memory location at offset x from FP *)
                  | InReg of Temp.temp (* value held in register *)
  datatype frag = PROC of {body: Tree.stm, frame: frame}
                | STRING of Temp.label * string
  
(* NOTE for AMD64 we are going to treat everything as an 8 byte entity 
this will work for use because we can use "long ints" for our ints and 
the pointers are already 8 bytes
If we need to deal with passign a 4 byte int to an external C function we will make it happen
by putting a wrapper around the C function call over in the runtime system code and do any
conversion needed in the C runtime code not in our tiger compiler
*)
val wordsize = 8 (*bytes*)

(* registers *)
(* Appel used all caps for the register names on the MIPS 
It looked ugly and non-standard to me for the AMD registers so I used lower case
*)
  val rax = Temp.newtemp() (* Return Value *)
                           
 
  (* Function Arguments *)
  val rdi  = Temp.newtemp()   (* argument #1 *)
  val rsi = Temp.newtemp()    (* argument #2 *)                  
  val rdx = Temp.newtemp()    (* argument #3 *)
  val rcx = Temp.newtemp()    (* argument #4 *)
  val r8  = Temp.newtemp()    (* argument #5 *)
  val r9  = Temp.newtemp()    (* argument #6 *)                 
                      
  val rsp = Temp.newtemp() (* Stack Pointer *)
 
 
  val registers = [ "rsp","rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15" ]
  val registerTemps = [rax, rbx, rcx, rdx, rsi, rdi, rbp, r8, r9, r10, r11, r12, r13, r14, r15]
  (* Appel doesn't want any of the four sets to overlap so even though we think of the args registers as caller saves
     they are not listed that way here*)

  (* Register Lists - Page 208 *)
  val argregs = [rdi, rsi, rdx, rcx, r8, r9]
  val calleesaves = [rbx, r12, r13, r14, r15]
  val callersaves = [rax, r10, r11]
  (* the list below will depend on how you intend to compute your stack frame offsets *)	
  val specialregs = [esp,rbp]
  (* NOTE if you are going to use rbp as a reference to frame offsets take it out of the list of colorables *)		       
  val colorable = calleesaves @ callersaves

  val tempMap =
    List.foldl
      (fn ((key, value), table) => Temp.Table.enter(table, key, value))
        Temp.Table.empty
          (ListPair.zip(registerTemps, registers))
      
  val calldefs = callersaves
  fun newFrame({name, formals}) = {name=name, formals=formals, locals=ref 0}
  
  fun name(f:frame) = #name f
  
  (* NOTE for the amd64 in order to use negative offsets from the beginning of a frame we need to have our entry code 
     save rsp into rbp after pushing rbp.  
     so this way of doing it implies the sequence
     pushq %rbp
     move %rsp, %rbp
     now we can use negative offsets to get to the saved formals and locals 
     If you want to only use rsp and use positive offsets, in allocating your locals note each in a list or stack. When you have seen 
     them all go back and "backpatch" the offsets. 
   *)

  fun formalToAcc(b:bool, offet:int ref) = case b of
					       true => (!offet = !offet + 1;
							InFrame(0 - !offet * wordsize))
					     | false => InReg(Temp.newtemp())
  fun formals(f:frame) = let
    (* escacc is really just how many formals and locals we have as we are assuming everything escapes *)
      val escacc = ref 0
      fun formalAccs([]) = []
        | formalAccs(h::r) = formalToAcc(h, escacc)::formalAccs(r)
  in
      formalAccs (#formals f)
  end
			     
  fun allocLocal(f:frame) = fn(b) => let
                                val escacc = #locals f
                            in
                                !escacc = !escacc + 1;
                                formalToAcc(b, escacc)
                            end
  (* In chapter 6 you really don't need the body of this yet as the Tree is the IR form we build in chapter 7 *)
  fun exp(InFrame(k)) =
      (fn (fp) => Tree.MEM(Tree.BINOP(Tree.PLUS, fp, Tree.CONST(k))))
    | exp (InReg(temp)) = (fn (fp) => Tree.TEMP(temp))
			      
 (* Just an assembly language statement to put a string in memory and have a label to refer to it *)
  fun string (label, str) =
      (Symbol.name label ^ ": .asciiz \"" ^ str ^ "\"\n")

(* just some IR code to move something from a regiser to memory *)	  
  fun move (reg, var) = Tree.MOVE (Tree.TEMP reg, Tree.TEMP var)
(* an expression sequence in the IR *)
  fun seq [] = Tree.EXP (Tree.CONST 0)
    | seq [exp] = exp
    | seq (exp :: exps) = (Tree.SEQ (exp, (seq exps)))

(* A call to one of our "library" routines implemented in the C code runtime.c *)			      
  fun externalCall (str, args) = Tree.CALL(Tree.NAME(Temp.namedlabel str), args)
					  
(* DOn't really need the body of this till chapter 7 *) 
  fun procEntryExit1 (frame, stm) =
      let
	  val saved = calleesaves
	  val temps = map (fn temp => Temp.newtemp ()) saved
	  val RS = seq (ListPair.mapEq move (temps, saved))
	  val RR = seq (ListPair.mapEq move (saved, temps))
	  val stm' = seq [RS, stm, RR]
			 
	  fun moveargs (arg, access) =
	      let
		  val access' = exp access
	      in
		  Tree.MOVE (access' (Tree.TEMP FP), Tree.TEMP arg)
	      end
		  
	  val funFormals = formals frame
	  (* we shouldn't need the viewshift as this is a RISC thing that the AMD64 doesn't have *)
	  val viewShift = seq (ListPair.map moveargs (argregs, funFormals))
			      
      in
	   stm
      end
	  
  structure A = Assem
  (* Pg 209 *)
  (* This appends a "sink" instruction to the function body to tell the 
     register allocator that certain registers are live at procedure exit. In our
     case it should be sufficient to list the special registers rsp and rbp if you are using it and 
     the calleesaves.
   *)
  fun procEntryExit2 (frame,body) =
      body @
      [A.OPER{assem="",
              src=specialregs @ calleesaves,
              dst=[],jump=SOME[]}]
	  
  (* Pg 209 *)
  (* this is a dummy "scaffold" version of this function that
     puts a dummy prolog and epilog into the code at this point 
   *)
  fun procEntryExit3 ({name=name, formals=formals, locals=locals}:frame,
                      body : Assem.instr list) =
      {prolog = "PROCEDURE " ^ Symbol.name name ^ "\n",
       body = body,
       epilog = "END " ^ Symbol.name name ^ "\n"}
	  
end
