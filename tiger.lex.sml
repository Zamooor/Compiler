functor TigerLexFun(structure Tokens: Tiger_TOKENS)  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof s = not (isSome (getc s))

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
STRING | COMMENT | INITIAL
    structure UserDeclarations = 
      struct

type pos = int
type svalue = Tokens.svalue
type pos = int
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val nesting = ref 0;
val inQuotes = ref false;
val catedString = ref "";
val stringYYpos = ref 0;
fun err(p1,p2) = ErrorMsg.error p1
fun eof() = 
(
    let 
        val pos = hd(!linePos) 
    in
        if (!nesting) <> 0 then
            ErrorMsg.error pos ("Unclosed comment") 
        else 
            print("");
        if (!inQuotes) <> false then
            ErrorMsg.error pos ("unclosed string")
        else
            print("");
    
    
        Tokens.EOF(pos,pos) 
    end
);

        



      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
Vector.fromList []
    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ()) = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = (yystrm := strm;
      (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue()))
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := ""; inQuotes := true; stringYYpos := yypos; YYBEGIN STRING; continue()))
fun yyAction2 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\n"; continue()))
fun yyAction3 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\t"; continue()))
fun yyAction4 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (catedString := (!catedString) ^ Char.toString(chr(Option.valOf(Int.fromString(String.substring(yytext, 1, size(yytext) - 1))))); continue())
      end
fun yyAction5 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (ErrorMsg.error yypos ("ignoring illegal excape sequence " ^ yytext); continue())
      end
fun yyAction6 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\""; continue()))
fun yyAction7 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\\"; continue()))
fun yyAction8 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^A"; continue()))
fun yyAction9 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^B"; continue()))
fun yyAction10 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^C"; continue()))
fun yyAction11 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^D"; continue()))
fun yyAction12 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^E"; continue()))
fun yyAction13 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^F"; continue()))
fun yyAction14 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^G"; continue()))
fun yyAction15 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^H"; continue()))
fun yyAction16 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^I"; continue()))
fun yyAction17 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^J"; continue()))
fun yyAction18 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^K"; continue()))
fun yyAction19 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^L"; continue()))
fun yyAction20 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^M"; continue()))
fun yyAction21 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^N"; continue()))
fun yyAction22 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^O"; continue()))
fun yyAction23 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^P"; continue()))
fun yyAction24 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^Q"; continue()))
fun yyAction25 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^R"; continue()))
fun yyAction26 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^S"; continue()))
fun yyAction27 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^T"; continue()))
fun yyAction28 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^U"; continue()))
fun yyAction29 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^V"; continue()))
fun yyAction30 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^W"; continue()))
fun yyAction31 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^X"; continue()))
fun yyAction32 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^Y"; continue()))
fun yyAction33 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^Z"; continue()))
fun yyAction34 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^["; continue()))
fun yyAction35 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^]"; continue()))
fun yyAction36 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^^"; continue()))
fun yyAction37 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^_"; continue()))
fun yyAction38 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ "\^@"; continue()))
fun yyAction39 (strm, lastMatch : yymatch) = (yystrm := strm;
      (catedString := (!catedString) ^ String.substring("\^\ ", 0, 1); continue()))
fun yyAction40 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction41 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (ErrorMsg.error yypos ("ignoring illegal excape character " ^ yytext); continue())
      end
fun yyAction42 (strm, lastMatch : yymatch) = (yystrm := strm;
      (inQuotes := false; YYBEGIN INITIAL; Tokens.STRING((!catedString), (!stringYYpos), (!stringYYpos)+size (!catedString))))
fun yyAction43 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (catedString := (!catedString) ^ yytext; continue())
      end
fun yyAction44 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (ErrorMsg.error yypos ("Expected a \" to close a string, instead found a new line" ^ yytext); lineNum := !lineNum+1; linePos := yypos :: !linePos; continue())
      end
fun yyAction45 (strm, lastMatch : yymatch) = (yystrm := strm;
      (nesting := (!nesting) + 1; YYBEGIN COMMENT; continue()))
fun yyAction46 (strm, lastMatch : yymatch) = (yystrm := strm;
      (nesting := (!nesting) + 1; continue()))
fun yyAction47 (strm, lastMatch : yymatch) = (yystrm := strm;
      (nesting := (!nesting) - 1; if (!nesting) = 0 then YYBEGIN INITIAL else (); continue()))
fun yyAction48 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction49 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TYPE(yypos, yypos+4)))
fun yyAction50 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.VAR(yypos, yypos+3)))
fun yyAction51 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.FUNCTION(yypos, yypos+8)))
fun yyAction52 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.BREAK(yypos, yypos+5)))
fun yyAction53 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.OF(yypos, yypos+2)))
fun yyAction54 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.END(yypos, yypos+3)))
fun yyAction55 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.IN(yypos, yypos+2)))
fun yyAction56 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.NIL(yypos, yypos+3)))
fun yyAction57 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LET(yypos, yypos+3)))
fun yyAction58 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DO(yypos, yypos+2)))
fun yyAction59 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TO(yypos, yypos+2)))
fun yyAction60 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.FOR(yypos, yypos+3)))
fun yyAction61 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.WHILE(yypos, yypos+5)))
fun yyAction62 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ELSE(yypos, yypos+4)))
fun yyAction63 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.IF(yypos, yypos+2)))
fun yyAction64 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.THEN(yypos, yypos+4)))
fun yyAction65 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ARRAY(yypos, yypos+5)))
fun yyAction66 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DIVIDE(yypos, yypos+1)))
fun yyAction67 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.TIMES(yypos, yypos+1)))
fun yyAction68 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.PLUS(yypos, yypos+1)))
fun yyAction69 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.MINUS(yypos, yypos+1)))
fun yyAction70 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOT(yypos, yypos+1)))
fun yyAction71 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LBRACE(yypos, yypos+1)))
fun yyAction72 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RBRACE(yypos, yypos+1)))
fun yyAction73 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LBRACK(yypos, yypos+1)))
fun yyAction74 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RBRACK(yypos, yypos+1)))
fun yyAction75 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LPAREN(yypos, yypos+1)))
fun yyAction76 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RPAREN(yypos, yypos+1)))
fun yyAction77 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.SEMICOLON(yypos, yypos+1)))
fun yyAction78 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.COLON(yypos, yypos+1)))
fun yyAction79 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.COMMA(yypos, yypos+1)))
fun yyAction80 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.AND(yypos, yypos+1)))
fun yyAction81 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.OR(yypos, yypos+1)))
fun yyAction82 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.EQ(yypos, yypos+1)))
fun yyAction83 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.NEQ(yypos, yypos+2)))
fun yyAction84 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.GE(yypos, yypos+2)))
fun yyAction85 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.GT(yypos, yypos+1)))
fun yyAction86 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LE(yypos, yypos+2)))
fun yyAction87 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LT(yypos, yypos+1)))
fun yyAction88 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.ASSIGN(yypos, yypos+2)))
fun yyAction89 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (Tokens.INT(Option.valOf (Int.fromString yytext),yypos,yypos+size yytext))
      end
fun yyAction90 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.ID(yytext,yypos,yypos+size yytext))
      end
fun yyAction91 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction92 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction93 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction94 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (ErrorMsg.error yypos ("illegal character " ^ yytext); continue())
      end
fun yyQ96 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction72(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction72(strm, yyNO_MATCH)
      (* end case *))
fun yyQ97 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction90(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction90(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction90(strm, yyNO_MATCH)
                  else yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ98 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction90(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction90(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction90(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ95 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction81(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction81, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction81(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction81(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction81, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction81, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction81(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction81, yyNO_MATCH))
                  else yyAction81(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction81(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction81(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction81, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction81, yyNO_MATCH))
              else yyAction81(strm, yyNO_MATCH)
      (* end case *))
fun yyQ94 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction71(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction71(strm, yyNO_MATCH)
      (* end case *))
fun yyQ102 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction61(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction61, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction61(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction61(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction61, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction61, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction61(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction61, yyNO_MATCH))
                  else yyAction61(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction61(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction61(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction61, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction61, yyNO_MATCH))
              else yyAction61(strm, yyNO_MATCH)
      (* end case *))
fun yyQ101 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"e"
                  then yyQ102(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ100 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"l"
                  then yyQ101(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ99 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"i"
                  then yyQ100(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ93 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"h"
                  then yyQ99(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ104 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction50(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction50, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction50(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction50(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction50, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction50, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction50(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction50, yyNO_MATCH))
                  else yyAction50(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction50(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction50(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction50, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction50, yyNO_MATCH))
              else yyAction50(strm, yyNO_MATCH)
      (* end case *))
fun yyQ103 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"r"
                  then yyQ104(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ92 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"a"
                  then yyQ103(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ109 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction49(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction49(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction49(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction49(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
                  else yyAction49(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction49(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction49(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction49, yyNO_MATCH))
              else yyAction49(strm, yyNO_MATCH)
      (* end case *))
fun yyQ108 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"e"
                  then yyQ109(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ107 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"p"
                  then yyQ108(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ106 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction59(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction59, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction59(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction59(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction59, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction59, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction59(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction59, yyNO_MATCH))
                  else yyAction59(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction59(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction59(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction59, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction59, yyNO_MATCH))
              else yyAction59(strm, yyNO_MATCH)
      (* end case *))
fun yyQ111 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction64(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction64, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction64(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction64(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction64, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction64, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction64(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction64, yyNO_MATCH))
                  else yyAction64(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction64(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction64(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction64, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction64, yyNO_MATCH))
              else yyAction64(strm, yyNO_MATCH)
      (* end case *))
fun yyQ110 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"n"
                  then yyQ111(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ105 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"e"
                  then yyQ110(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ91 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"h"
              then yyQ105(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"h"
              then if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then if inp = #":"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp < #":"
                      then if inp <= #"/"
                          then yyAction90(strm, yyNO_MATCH)
                          else yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp <= #"@"
                      then yyAction90(strm, yyNO_MATCH)
                      else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"`"
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"`"
                  then if inp = #"_"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"z"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"z"
              then if inp = #"p"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"p"
                  then if inp = #"o"
                      then yyQ106(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"y"
                  then yyQ107(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ112 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction53(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction53, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction53(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction53(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction53, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction53, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction53(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction53, yyNO_MATCH))
                  else yyAction53(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction53(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction53(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction53, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction53, yyNO_MATCH))
              else yyAction53(strm, yyNO_MATCH)
      (* end case *))
fun yyQ90 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"f"
                  then yyQ112(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ114 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction56(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction56, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction56(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction56(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction56, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction56, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction56(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction56, yyNO_MATCH))
                  else yyAction56(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction56(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction56(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction56, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction56, yyNO_MATCH))
              else yyAction56(strm, yyNO_MATCH)
      (* end case *))
fun yyQ113 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"l"
                  then yyQ114(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ89 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"i"
                  then yyQ113(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ116 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction57(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction57, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction57(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction57(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction57, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction57, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction57(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction57, yyNO_MATCH))
                  else yyAction57(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction57(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction57(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction57, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction57, yyNO_MATCH))
              else yyAction57(strm, yyNO_MATCH)
      (* end case *))
fun yyQ115 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"t"
                  then yyQ116(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ88 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"e"
                  then yyQ115(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ118 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction55(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction55, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction55(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction55(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction55, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction55, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction55(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction55, yyNO_MATCH))
                  else yyAction55(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction55(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction55(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction55, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction55, yyNO_MATCH))
              else yyAction55(strm, yyNO_MATCH)
      (* end case *))
fun yyQ117 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction63(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction63, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction63(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction63(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction63, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction63, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction63(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction63, yyNO_MATCH))
                  else yyAction63(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction63(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction63(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction63, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction63, yyNO_MATCH))
              else yyAction63(strm, yyNO_MATCH)
      (* end case *))
fun yyQ87 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"_"
                  then if inp <= #"Z"
                      then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"o"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"o"
              then if inp = #"g"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"g"
                  then if inp = #"f"
                      then yyQ117(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"n"
                  then yyQ118(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction90(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ126 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction51(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction51, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction51(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction51(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction51, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction51, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction51(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction51, yyNO_MATCH))
                  else yyAction51(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction51(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction51(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction51, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction51, yyNO_MATCH))
              else yyAction51(strm, yyNO_MATCH)
      (* end case *))
fun yyQ125 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"n"
                  then yyQ126(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ124 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"o"
                  then yyQ125(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ123 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"i"
                  then yyQ124(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ122 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"t"
                  then yyQ123(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ121 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"c"
                  then yyQ122(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ120 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"n"
                  then yyQ121(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ127 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction60(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction60, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction60(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction60(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction60, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction60, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction60(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction60, yyNO_MATCH))
                  else yyAction60(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction60(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction60(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction60, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction60, yyNO_MATCH))
              else yyAction60(strm, yyNO_MATCH)
      (* end case *))
fun yyQ119 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"r"
                  then yyQ127(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ86 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"_"
                  then if inp <= #"Z"
                      then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"v"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"v"
              then if inp = #"p"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"p"
                  then if inp = #"o"
                      then yyQ119(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"u"
                  then yyQ120(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction90(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ130 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction54(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction54, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction54(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction54(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction54, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction54, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction54(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction54, yyNO_MATCH))
                  else yyAction54(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction54(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction54(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction54, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction54, yyNO_MATCH))
              else yyAction54(strm, yyNO_MATCH)
      (* end case *))
fun yyQ129 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"d"
                  then yyQ130(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ132 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction62(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction62, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction62(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction62(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction62, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction62, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction62(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction62, yyNO_MATCH))
                  else yyAction62(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction62(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction62(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction62, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction62, yyNO_MATCH))
              else yyAction62(strm, yyNO_MATCH)
      (* end case *))
fun yyQ131 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"e"
                  then yyQ132(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ128 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"s"
                  then yyQ131(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ85 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"a"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"a"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"_"
                  then if inp <= #"Z"
                      then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"o"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"o"
              then if inp = #"m"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"m"
                  then if inp = #"l"
                      then yyQ128(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ129(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"|"
              then if inp = #"{"
                  then yyAction90(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ133 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction58(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction58(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction58(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction58(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
                  else yyAction58(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction58(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction58(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction58, yyNO_MATCH))
              else yyAction58(strm, yyNO_MATCH)
      (* end case *))
fun yyQ84 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"o"
                  then yyQ133(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ137 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction52(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction52(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction52(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction52(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
                  else yyAction52(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction52(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction52(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction52, yyNO_MATCH))
              else yyAction52(strm, yyNO_MATCH)
      (* end case *))
fun yyQ136 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"k"
                  then yyQ137(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ135 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"a"
                  then yyQ136(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ134 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"e"
                  then yyQ135(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ83 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"r"
                  then yyQ134(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ141 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction65(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction65, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction65(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction65(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction65, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction65, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction65(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction65, yyNO_MATCH))
                  else yyAction65(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction65(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction65(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction65, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction65, yyNO_MATCH))
              else yyAction65(strm, yyNO_MATCH)
      (* end case *))
fun yyQ140 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"y"
                  then yyQ141(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ139 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"a"
                  then yyQ140(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ138 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"r"
                  then yyQ139(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ82 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"`"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then if inp = #"0"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                    else if inp < #"0"
                      then yyAction90(strm, yyNO_MATCH)
                    else if inp <= #"9"
                      then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                      else yyAction90(strm, yyNO_MATCH)
                else if inp = #"["
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"r"
                  then yyQ138(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ81 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction74(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction74(strm, yyNO_MATCH)
      (* end case *))
fun yyQ80 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction73(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction73(strm, yyNO_MATCH)
      (* end case *))
fun yyQ79 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction90(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"_"
              then yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #":"
                  then yyAction90(strm, yyNO_MATCH)
                else if inp < #":"
                  then if inp <= #"/"
                      then yyAction90(strm, yyNO_MATCH)
                      else yyQ97(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                else if inp < #"A"
                  then yyAction90(strm, yyNO_MATCH)
                else if inp <= #"Z"
                  then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
                  else yyAction90(strm, yyNO_MATCH)
            else if inp = #"{"
              then yyAction90(strm, yyNO_MATCH)
            else if inp < #"{"
              then if inp = #"`"
                  then yyAction90(strm, yyNO_MATCH)
                  else yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
            else if inp = #"|"
              then yyQ98(strm', yyMATCH(strm, yyAction90, yyNO_MATCH))
              else yyAction90(strm, yyNO_MATCH)
      (* end case *))
fun yyQ142 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction84(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction84(strm, yyNO_MATCH)
      (* end case *))
fun yyQ78 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction85(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"="
              then yyQ142(strm', yyMATCH(strm, yyAction85, yyNO_MATCH))
              else yyAction85(strm, yyNO_MATCH)
      (* end case *))
fun yyQ77 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction82(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction82(strm, yyNO_MATCH)
      (* end case *))
fun yyQ144 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction83(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction83(strm, yyNO_MATCH)
      (* end case *))
fun yyQ143 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction86(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction86(strm, yyNO_MATCH)
      (* end case *))
fun yyQ76 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction87(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #">"
              then yyQ144(strm', yyMATCH(strm, yyAction87, yyNO_MATCH))
            else if inp < #">"
              then if inp = #"="
                  then yyQ143(strm', yyMATCH(strm, yyAction87, yyNO_MATCH))
                  else yyAction87(strm, yyNO_MATCH)
              else yyAction87(strm, yyNO_MATCH)
      (* end case *))
fun yyQ75 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction77(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction77(strm, yyNO_MATCH)
      (* end case *))
fun yyQ145 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction88(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction88(strm, yyNO_MATCH)
      (* end case *))
fun yyQ74 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction78(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"="
              then yyQ145(strm', yyMATCH(strm, yyAction78, yyNO_MATCH))
              else yyAction78(strm, yyNO_MATCH)
      (* end case *))
fun yyQ146 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction89(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ146(strm', yyMATCH(strm, yyAction89, yyNO_MATCH))
            else if inp < #"0"
              then yyAction89(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ146(strm', yyMATCH(strm, yyAction89, yyNO_MATCH))
              else yyAction89(strm, yyNO_MATCH)
      (* end case *))
fun yyQ73 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction89(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ146(strm', yyMATCH(strm, yyAction89, yyNO_MATCH))
            else if inp < #"0"
              then yyAction89(strm, yyNO_MATCH)
            else if inp <= #"9"
              then yyQ146(strm', yyMATCH(strm, yyAction89, yyNO_MATCH))
              else yyAction89(strm, yyNO_MATCH)
      (* end case *))
fun yyQ147 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction45(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction45(strm, yyNO_MATCH)
      (* end case *))
fun yyQ72 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction66(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ147(strm', yyMATCH(strm, yyAction66, yyNO_MATCH))
              else yyAction66(strm, yyNO_MATCH)
      (* end case *))
fun yyQ71 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction70(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction70(strm, yyNO_MATCH)
      (* end case *))
fun yyQ70 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction69(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction69(strm, yyNO_MATCH)
      (* end case *))
fun yyQ69 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction79(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction79(strm, yyNO_MATCH)
      (* end case *))
fun yyQ68 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction68(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction68(strm, yyNO_MATCH)
      (* end case *))
fun yyQ67 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction67(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction67(strm, yyNO_MATCH)
      (* end case *))
fun yyQ66 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction76(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction76(strm, yyNO_MATCH)
      (* end case *))
fun yyQ65 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction75(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction75(strm, yyNO_MATCH)
      (* end case *))
fun yyQ64 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction80(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction80(strm, yyNO_MATCH)
      (* end case *))
fun yyQ63 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ62 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction91(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction91(strm, yyNO_MATCH)
      (* end case *))
fun yyQ55 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ61 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction92(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction92(strm, yyNO_MATCH)
      (* end case *))
fun yyQ60 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction94(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction94(strm, yyNO_MATCH)
      (* end case *))
fun yyQ2 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"["
              then yyQ80(strm', lastMatch)
            else if inp < #"["
              then if inp = #"+"
                  then yyQ68(strm', lastMatch)
                else if inp < #"+"
                  then if inp = #"\""
                      then yyQ63(strm', lastMatch)
                    else if inp < #"\""
                      then if inp = #"\v"
                          then yyQ60(strm', lastMatch)
                        else if inp < #"\v"
                          then if inp = #"\t"
                              then yyQ61(strm', lastMatch)
                            else if inp = #"\n"
                              then yyQ55(strm', lastMatch)
                              else yyQ60(strm', lastMatch)
                        else if inp = #" "
                          then yyQ62(strm', lastMatch)
                          else yyQ60(strm', lastMatch)
                    else if inp = #"("
                      then yyQ65(strm', lastMatch)
                    else if inp < #"("
                      then if inp = #"&"
                          then yyQ64(strm', lastMatch)
                          else yyQ60(strm', lastMatch)
                    else if inp = #")"
                      then yyQ66(strm', lastMatch)
                      else yyQ67(strm', lastMatch)
                else if inp = #";"
                  then yyQ75(strm', lastMatch)
                else if inp < #";"
                  then if inp = #"/"
                      then yyQ72(strm', lastMatch)
                    else if inp < #"/"
                      then if inp = #"-"
                          then yyQ70(strm', lastMatch)
                        else if inp = #","
                          then yyQ69(strm', lastMatch)
                          else yyQ71(strm', lastMatch)
                    else if inp = #":"
                      then yyQ74(strm', lastMatch)
                      else yyQ73(strm', lastMatch)
                else if inp = #">"
                  then yyQ78(strm', lastMatch)
                else if inp < #">"
                  then if inp = #"<"
                      then yyQ76(strm', lastMatch)
                      else yyQ77(strm', lastMatch)
                else if inp <= #"@"
                  then yyQ60(strm', lastMatch)
                  else yyQ79(strm', lastMatch)
            else if inp = #"m"
              then yyQ79(strm', lastMatch)
            else if inp < #"m"
              then if inp = #"d"
                  then yyQ84(strm', lastMatch)
                else if inp < #"d"
                  then if inp = #"a"
                      then yyQ82(strm', lastMatch)
                    else if inp < #"a"
                      then if inp = #"]"
                          then yyQ81(strm', lastMatch)
                          else yyQ60(strm', lastMatch)
                    else if inp = #"b"
                      then yyQ83(strm', lastMatch)
                      else yyQ79(strm', lastMatch)
                else if inp = #"i"
                  then yyQ87(strm', lastMatch)
                else if inp < #"i"
                  then if inp = #"f"
                      then yyQ86(strm', lastMatch)
                    else if inp = #"e"
                      then yyQ85(strm', lastMatch)
                      else yyQ79(strm', lastMatch)
                else if inp = #"l"
                  then yyQ88(strm', lastMatch)
                  else yyQ79(strm', lastMatch)
            else if inp = #"w"
              then yyQ93(strm', lastMatch)
            else if inp < #"w"
              then if inp = #"t"
                  then yyQ91(strm', lastMatch)
                else if inp < #"t"
                  then if inp = #"o"
                      then yyQ90(strm', lastMatch)
                    else if inp = #"n"
                      then yyQ89(strm', lastMatch)
                      else yyQ79(strm', lastMatch)
                else if inp = #"u"
                  then yyQ79(strm', lastMatch)
                  else yyQ92(strm', lastMatch)
            else if inp = #"|"
              then yyQ95(strm', lastMatch)
            else if inp < #"|"
              then if inp = #"{"
                  then yyQ94(strm', lastMatch)
                  else yyQ79(strm', lastMatch)
            else if inp = #"}"
              then yyQ96(strm', lastMatch)
              else yyQ60(strm', lastMatch)
      (* end case *))
fun yyQ58 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction46(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction46(strm, yyNO_MATCH)
      (* end case *))
fun yyQ57 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ58(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
              else yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ59 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction47(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction47(strm, yyNO_MATCH)
      (* end case *))
fun yyQ56 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"/"
              then yyQ59(strm', yyMATCH(strm, yyAction48, yyNO_MATCH))
              else yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ54 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction48(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction48(strm, yyNO_MATCH)
      (* end case *))
fun yyQ1 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ56(strm', lastMatch)
            else if inp < #"*"
              then if inp = #"\n"
                  then yyQ55(strm', lastMatch)
                  else yyQ54(strm', lastMatch)
            else if inp = #"/"
              then yyQ57(strm', lastMatch)
              else yyQ54(strm', lastMatch)
      (* end case *))
fun yyQ15 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction3(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction3(strm, yyNO_MATCH)
      (* end case *))
fun yyQ14 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ47 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction37(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction37(strm, yyNO_MATCH)
      (* end case *))
fun yyQ46 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction36(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction36(strm, yyNO_MATCH)
      (* end case *))
fun yyQ45 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction35(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction35(strm, yyNO_MATCH)
      (* end case *))
fun yyQ44 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction39(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction39(strm, yyNO_MATCH)
      (* end case *))
fun yyQ43 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction34(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction34(strm, yyNO_MATCH)
      (* end case *))
fun yyQ42 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction33(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction33(strm, yyNO_MATCH)
      (* end case *))
fun yyQ41 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction32(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction32(strm, yyNO_MATCH)
      (* end case *))
fun yyQ40 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction31(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction31(strm, yyNO_MATCH)
      (* end case *))
fun yyQ39 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction30(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction30(strm, yyNO_MATCH)
      (* end case *))
fun yyQ38 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction29(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction29(strm, yyNO_MATCH)
      (* end case *))
fun yyQ37 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction28(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction28(strm, yyNO_MATCH)
      (* end case *))
fun yyQ36 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction27(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction27(strm, yyNO_MATCH)
      (* end case *))
fun yyQ35 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction26(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction26(strm, yyNO_MATCH)
      (* end case *))
fun yyQ34 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction25(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction25(strm, yyNO_MATCH)
      (* end case *))
fun yyQ33 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction24(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction24(strm, yyNO_MATCH)
      (* end case *))
fun yyQ32 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction23(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction23(strm, yyNO_MATCH)
      (* end case *))
fun yyQ31 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction22(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction22(strm, yyNO_MATCH)
      (* end case *))
fun yyQ30 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction21(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction21(strm, yyNO_MATCH)
      (* end case *))
fun yyQ29 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction20(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction20(strm, yyNO_MATCH)
      (* end case *))
fun yyQ28 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction19(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction19(strm, yyNO_MATCH)
      (* end case *))
fun yyQ27 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction18(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction18(strm, yyNO_MATCH)
      (* end case *))
fun yyQ26 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ25 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction16(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction16(strm, yyNO_MATCH)
      (* end case *))
fun yyQ24 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction15(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction15(strm, yyNO_MATCH)
      (* end case *))
fun yyQ23 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction14(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction14(strm, yyNO_MATCH)
      (* end case *))
fun yyQ22 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction13(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction13(strm, yyNO_MATCH)
      (* end case *))
fun yyQ21 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction12(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction12(strm, yyNO_MATCH)
      (* end case *))
fun yyQ20 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction11(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction11(strm, yyNO_MATCH)
      (* end case *))
fun yyQ19 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ18 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction9(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction9(strm, yyNO_MATCH)
      (* end case *))
fun yyQ17 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction8(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction8(strm, yyNO_MATCH)
      (* end case *))
fun yyQ16 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction38(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction38(strm, yyNO_MATCH)
      (* end case *))
fun yyQ13 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"]"
              then yyQ45(strm', lastMatch)
            else if inp < #"]"
              then if inp = #"N"
                  then yyQ30(strm', lastMatch)
                else if inp < #"N"
                  then if inp = #"F"
                      then yyQ22(strm', lastMatch)
                    else if inp < #"F"
                      then if inp = #"B"
                          then yyQ18(strm', lastMatch)
                        else if inp < #"B"
                          then if inp = #"@"
                              then yyQ16(strm', lastMatch)
                            else if inp = #"A"
                              then yyQ17(strm', lastMatch)
                              else yystuck(lastMatch)
                        else if inp = #"D"
                          then yyQ20(strm', lastMatch)
                        else if inp = #"C"
                          then yyQ19(strm', lastMatch)
                          else yyQ21(strm', lastMatch)
                    else if inp = #"J"
                      then yyQ26(strm', lastMatch)
                    else if inp < #"J"
                      then if inp = #"H"
                          then yyQ24(strm', lastMatch)
                        else if inp = #"G"
                          then yyQ23(strm', lastMatch)
                          else yyQ25(strm', lastMatch)
                    else if inp = #"L"
                      then yyQ28(strm', lastMatch)
                    else if inp = #"K"
                      then yyQ27(strm', lastMatch)
                      else yyQ29(strm', lastMatch)
                else if inp = #"V"
                  then yyQ38(strm', lastMatch)
                else if inp < #"V"
                  then if inp = #"R"
                      then yyQ34(strm', lastMatch)
                    else if inp < #"R"
                      then if inp = #"P"
                          then yyQ32(strm', lastMatch)
                        else if inp = #"O"
                          then yyQ31(strm', lastMatch)
                          else yyQ33(strm', lastMatch)
                    else if inp = #"T"
                      then yyQ36(strm', lastMatch)
                    else if inp = #"S"
                      then yyQ35(strm', lastMatch)
                      else yyQ37(strm', lastMatch)
                else if inp = #"Z"
                  then yyQ42(strm', lastMatch)
                else if inp < #"Z"
                  then if inp = #"X"
                      then yyQ40(strm', lastMatch)
                    else if inp = #"W"
                      then yyQ39(strm', lastMatch)
                      else yyQ41(strm', lastMatch)
                else if inp = #"["
                  then yyQ43(strm', lastMatch)
                  else yyQ44(strm', lastMatch)
            else if inp = #"m"
              then yyQ29(strm', lastMatch)
            else if inp < #"m"
              then if inp = #"e"
                  then yyQ21(strm', lastMatch)
                else if inp < #"e"
                  then if inp = #"a"
                      then yyQ17(strm', lastMatch)
                    else if inp < #"a"
                      then if inp = #"_"
                          then yyQ47(strm', lastMatch)
                        else if inp = #"^"
                          then yyQ46(strm', lastMatch)
                          else yystuck(lastMatch)
                    else if inp = #"c"
                      then yyQ19(strm', lastMatch)
                    else if inp = #"b"
                      then yyQ18(strm', lastMatch)
                      else yyQ20(strm', lastMatch)
                else if inp = #"i"
                  then yyQ25(strm', lastMatch)
                else if inp < #"i"
                  then if inp = #"g"
                      then yyQ23(strm', lastMatch)
                    else if inp = #"f"
                      then yyQ22(strm', lastMatch)
                      else yyQ24(strm', lastMatch)
                else if inp = #"k"
                  then yyQ27(strm', lastMatch)
                else if inp = #"j"
                  then yyQ26(strm', lastMatch)
                  else yyQ28(strm', lastMatch)
            else if inp = #"u"
              then yyQ37(strm', lastMatch)
            else if inp < #"u"
              then if inp = #"q"
                  then yyQ33(strm', lastMatch)
                else if inp < #"q"
                  then if inp = #"o"
                      then yyQ31(strm', lastMatch)
                    else if inp = #"n"
                      then yyQ30(strm', lastMatch)
                      else yyQ32(strm', lastMatch)
                else if inp = #"s"
                  then yyQ35(strm', lastMatch)
                else if inp = #"r"
                  then yyQ34(strm', lastMatch)
                  else yyQ36(strm', lastMatch)
            else if inp = #"y"
              then yyQ41(strm', lastMatch)
            else if inp < #"y"
              then if inp = #"w"
                  then yyQ39(strm', lastMatch)
                else if inp = #"v"
                  then yyQ38(strm', lastMatch)
                  else yyQ40(strm', lastMatch)
            else if inp = #"z"
              then yyQ42(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ12 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction7(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction7(strm, yyNO_MATCH)
      (* end case *))
fun yyQ49 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction5(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction5(strm, yyNO_MATCH)
      (* end case *))
fun yyQ48 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ49(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ49(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ11 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ48(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ48(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ52 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ51 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"6"
              then yyQ49(strm', lastMatch)
            else if inp < #"6"
              then if inp <= #"/"
                  then yystuck(lastMatch)
                  else yyQ52(strm', lastMatch)
            else if inp <= #"9"
              then yyQ49(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ50 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ52(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ52(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ10 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"5"
              then yyQ51(strm', lastMatch)
            else if inp < #"5"
              then if inp <= #"/"
                  then yystuck(lastMatch)
                  else yyQ50(strm', lastMatch)
            else if inp <= #"9"
              then yyQ48(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ9 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"0"
              then yyQ50(strm', lastMatch)
            else if inp < #"0"
              then yystuck(lastMatch)
            else if inp <= #"9"
              then yyQ50(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ8 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction6(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction6(strm, yyNO_MATCH)
      (* end case *))
fun yyQ53 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction40(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction40(strm, yyNO_MATCH)
      (* end case *))
fun yyQ7 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\r"
              then yystuck(lastMatch)
            else if inp < #"\r"
              then if inp = #"\v"
                  then yystuck(lastMatch)
                else if inp < #"\v"
                  then if inp <= #"\a"
                      then yystuck(lastMatch)
                      else yyQ7(strm', lastMatch)
                  else yyQ7(strm', lastMatch)
            else if inp = #"!"
              then yystuck(lastMatch)
            else if inp < #"!"
              then if inp = #" "
                  then yyQ7(strm', lastMatch)
                  else yystuck(lastMatch)
            else if inp = #"\\"
              then yyQ53(strm', lastMatch)
              else yystuck(lastMatch)
      (* end case *))
fun yyQ6 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction41(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"2"
              then yyQ10(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
            else if inp < #"2"
              then if inp = #" "
                  then yyQ7(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
                else if inp < #" "
                  then if inp = #"\v"
                      then yyAction41(strm, yyNO_MATCH)
                    else if inp < #"\v"
                      then if inp <= #"\a"
                          then yyAction41(strm, yyNO_MATCH)
                          else yyQ7(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
                    else if inp = #"\f"
                      then yyQ7(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
                      else yyAction41(strm, yyNO_MATCH)
                else if inp = #"#"
                  then yyAction41(strm, yyNO_MATCH)
                else if inp < #"#"
                  then if inp = #"!"
                      then yyAction41(strm, yyNO_MATCH)
                      else yyQ8(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
                else if inp <= #"/"
                  then yyAction41(strm, yyNO_MATCH)
                  else yyQ9(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
            else if inp = #"_"
              then yyAction41(strm, yyNO_MATCH)
            else if inp < #"_"
              then if inp = #"\\"
                  then yyQ12(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
                else if inp < #"\\"
                  then if inp <= #"9"
                      then yyQ11(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
                      else yyAction41(strm, yyNO_MATCH)
                else if inp = #"]"
                  then yyAction41(strm, yyNO_MATCH)
                  else yyQ13(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
            else if inp = #"o"
              then yyAction41(strm, yyNO_MATCH)
            else if inp < #"o"
              then if inp = #"n"
                  then yyQ14(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
                  else yyAction41(strm, yyNO_MATCH)
            else if inp = #"t"
              then yyQ15(strm', yyMATCH(strm, yyAction41, yyNO_MATCH))
              else yyAction41(strm, yyNO_MATCH)
      (* end case *))
fun yyQ5 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction42(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction42(strm, yyNO_MATCH)
      (* end case *))
fun yyQ4 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction44(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction44(strm, yyNO_MATCH)
      (* end case *))
fun yyQ3 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction43(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction43(strm, yyNO_MATCH)
      (* end case *))
fun yyQ0 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\""
              then yyQ5(strm', lastMatch)
            else if inp < #"\""
              then if inp = #"\n"
                  then yyQ4(strm', lastMatch)
                  else yyQ3(strm', lastMatch)
            else if inp = #"\\"
              then yyQ6(strm', lastMatch)
              else yyQ3(strm', lastMatch)
      (* end case *))
in
  (case (!(yyss))
   of STRING => yyQ0(!(yystrm), yyNO_MATCH)
    | COMMENT => yyQ1(!(yystrm), yyNO_MATCH)
    | INITIAL => yyQ2(!(yystrm), yyNO_MATCH)
  (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    fun makeLexer' ins = mk (yyInput.mkStream ins)
    end

  end
