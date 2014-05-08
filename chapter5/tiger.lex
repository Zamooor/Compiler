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

        

%% 

digits=[0-9]+ ;
letters=[a-z|A-Z]+ ;
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s STRING COMMENT;


%%
<INITIAL,COMMENT>\n     => (catedString := ""; lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());

<INITIAL>["]            => (inQuotes := true; stringYYpos := yypos; YYBEGIN STRING; continue());
<STRING>"\\n"           => (catedString := (!catedString) ^ "\n"; continue());
<STRING>"\\t"           => (catedString := (!catedString) ^ "\t"; continue());
<STRING>("\\"([0-1][0-9]{2}|2[0-4][0-9]|25[0-5]))   
                        => (catedString := (!catedString) ^ Char.toString(chr(Option.valOf(Int.fromString(String.substring(yytext, 1, size(yytext) - 1))))); continue());                        
<STRING>("\\"([0-9]{3}))=> (ErrorMsg.error yypos ("ignoring illegal excape sequence " ^ yytext); continue());
<STRING>"\\"["]         => (catedString := (!catedString) ^ "\""; continue());
<STRING>"\\\\"          => (catedString := (!catedString) ^ "\\"; continue());
<STRING>("\\^"[aA])     => (catedString := (!catedString) ^ "\^A"; continue());
<STRING>("\\^"[bB])     => (catedString := (!catedString) ^ "\^B"; continue());
<STRING>("\\^"[cC])     => (catedString := (!catedString) ^ "\^C"; continue());
<STRING>("\\^"[dD])     => (catedString := (!catedString) ^ "\^D"; continue());
<STRING>("\\^"[eE])     => (catedString := (!catedString) ^ "\^E"; continue());
<STRING>("\\^"[fF])     => (catedString := (!catedString) ^ "\^F"; continue());
<STRING>("\\^"[gG])     => (catedString := (!catedString) ^ "\^G"; continue());
<STRING>("\\^"[hH])     => (catedString := (!catedString) ^ "\^H"; continue());
<STRING>("\\^"[iI])     => (catedString := (!catedString) ^ "\^I"; continue());
<STRING>("\\^"[jJ])     => (catedString := (!catedString) ^ "\^J"; continue());
<STRING>("\\^"[kK])     => (catedString := (!catedString) ^ "\^K"; continue());
<STRING>("\\^"[lL])     => (catedString := (!catedString) ^ "\^L"; continue());
<STRING>("\\^"[mM])     => (catedString := (!catedString) ^ "\^M"; continue());
<STRING>("\\^"[nN])     => (catedString := (!catedString) ^ "\^N"; continue());
<STRING>("\\^"[oO])     => (catedString := (!catedString) ^ "\^O"; continue());
<STRING>("\\^"[pP])     => (catedString := (!catedString) ^ "\^P"; continue());
<STRING>("\\^"[qQ])     => (catedString := (!catedString) ^ "\^Q"; continue());
<STRING>("\\^"[rR])     => (catedString := (!catedString) ^ "\^R"; continue());
<STRING>("\\^"[sS])     => (catedString := (!catedString) ^ "\^S"; continue());
<STRING>("\\^"[tT])     => (catedString := (!catedString) ^ "\^T"; continue());
<STRING>("\\^"[uU])     => (catedString := (!catedString) ^ "\^U"; continue());
<STRING>("\\^"[vV])     => (catedString := (!catedString) ^ "\^V"; continue());
<STRING>("\\^"[wW])     => (catedString := (!catedString) ^ "\^W"; continue());
<STRING>("\\^"[xX])     => (catedString := (!catedString) ^ "\^X"; continue());
<STRING>("\\^"[yY])     => (catedString := (!catedString) ^ "\^Y"; continue());
<STRING>("\\^"[zZ])     => (catedString := (!catedString) ^ "\^Z"; continue());
<STRING>("\\^[")        => (catedString := (!catedString) ^ "\^["; continue());
<STRING>("\\^]")        => (catedString := (!catedString) ^ "\^]"; continue());
<STRING>("\\^^")        => (catedString := (!catedString) ^ "\^^"; continue());
<STRING>("\\^_")        => (catedString := (!catedString) ^ "\^_"; continue());
<STRING>("\\^@")        => (catedString := (!catedString) ^ "\^@"; continue());
<STRING>"\\""^""\\"     => (catedString := (!catedString) ^ String.substring("\^\ ", 0, 1); continue());
<STRING>"\\"[\n\t\b\032\012]*"\\"         
                        => (continue());
<STRING>"\\"            => (ErrorMsg.error yypos ("ignoring illegal excape character " ^ yytext); continue());
<STRING>["]             => (inQuotes := false; YYBEGIN INITIAL; Tokens.STRING((!catedString), (!stringYYpos), (!stringYYpos)+size (!catedString)));
<STRING>.               => (catedString := (!catedString) ^ yytext; continue());
<STRING>\n              => (ErrorMsg.error yypos ("Expected a \" to close a string, instead found a new line" ^ yytext); lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());

<INITIAL>"/*"           => (nesting := (!nesting) + 1; YYBEGIN COMMENT; continue());
<COMMENT>"/*"           => (nesting := (!nesting) + 1; continue());
<COMMENT>"*/"           => (nesting := (!nesting) - 1; if (!nesting) = 0 then YYBEGIN INITIAL else (); continue());
<COMMENT>.              => (continue());



<INITIAL>type =>(Tokens.TYPE(yypos, yypos+4));
<INITIAL>var =>(Tokens.VAR(yypos, yypos+3));
<INITIAL>function =>(Tokens.FUNCTION(yypos, yypos+8));
<INITIAL>break =>(Tokens.BREAK(yypos, yypos+5));
<INITIAL>of =>(Tokens.OF(yypos, yypos+2));
<INITIAL>end =>(Tokens.END(yypos, yypos+3));
<INITIAL>in =>(Tokens.IN(yypos, yypos+2));
<INITIAL>nil =>(Tokens.NIL(yypos, yypos+3));
<INITIAL>let =>(Tokens.LET(yypos, yypos+3));
<INITIAL>do =>(Tokens.DO(yypos, yypos+2));
<INITIAL>to =>(Tokens.TO(yypos, yypos+2));
<INITIAL>for =>(Tokens.FOR(yypos, yypos+3));
<INITIAL>while =>(Tokens.WHILE(yypos, yypos+5));
<INITIAL>else =>(Tokens.ELSE(yypos, yypos+4));
<INITIAL>if =>(Tokens.IF(yypos, yypos+2));
<INITIAL>then =>(Tokens.THEN(yypos, yypos+4));
<INITIAL>array =>(Tokens.ARRAY(yypos, yypos+5));
<INITIAL>"/" =>(Tokens.DIVIDE(yypos, yypos+1));
<INITIAL>"*" =>(Tokens.TIMES(yypos, yypos+1));
<INITIAL>"+" =>(Tokens.PLUS(yypos, yypos+1));
<INITIAL>"-" =>(Tokens.MINUS(yypos, yypos+1));
<INITIAL>"." =>(Tokens.DOT(yypos, yypos+1));
<INITIAL>"{" =>(Tokens.LBRACE(yypos, yypos+1));
<INITIAL>"}" =>(Tokens.RBRACE(yypos, yypos+1));
<INITIAL>"[" =>(Tokens.LBRACK(yypos, yypos+1));
<INITIAL>"]" =>(Tokens.RBRACK(yypos, yypos+1));
<INITIAL>"(" =>(Tokens.LPAREN(yypos, yypos+1));
<INITIAL>")" =>(Tokens.RPAREN(yypos, yypos+1));
<INITIAL>";" =>(Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL>":" =>(Tokens.COLON(yypos, yypos+1));
<INITIAL>"," =>(Tokens.COMMA(yypos, yypos+1));
<INITIAL>"&" =>(Tokens.AND(yypos, yypos+1));
<INITIAL>"|" =>(Tokens.OR(yypos, yypos+1));
<INITIAL>"=" =>(Tokens.EQ(yypos, yypos+1));
<INITIAL>"<>" =>(Tokens.NEQ(yypos, yypos+2));
<INITIAL>">=" =>(Tokens.GE(yypos, yypos+2));
<INITIAL>">" =>(Tokens.GT(yypos, yypos+1));
<INITIAL>"<=" =>(Tokens.LE(yypos, yypos+2));
<INITIAL>"<" =>(Tokens.LT(yypos, yypos+1));
<INITIAL>":=" =>(Tokens.ASSIGN(yypos, yypos+2));

<INITIAL>{digits}	    => (Tokens.INT(Option.valOf (Int.fromString yytext),yypos,yypos+size yytext));


<INITIAL>{letters}[a-zA-Z|0-9|_]* 
                        => (Tokens.ID(yytext,yypos,yypos+size yytext));

<INITIAL>" "            => (continue());
<INITIAL>\t             => (continue());

<INITIAL>\t             => (continue());


<INITIAL>.              => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());

