structure Types =
struct

  type unique = unit ref

  datatype ty = 
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
          | STRING
          | ARRAY of ty * unique
	  | NAME of Symbol.symbol * ty option ref
	  | UNIT
	  
	  
  fun toString(ty) =
        case ty of INT =>
            "INT"
        | RECORD(fields,_) =>
            "RECORD "^Symbol.name(#1(List.hd(fields)))^" "^toString(#2(List.hd(fields)))^" "^Symbol.name(#1(List.nth(fields, 1)))^" "^toString(#2(List.nth(fields,1)))^" "
        | NIL =>
            "NIL"
        | STRING =>
            "STRING"
        | ARRAY(typ,ref()) =>
            "ARRAY"
        | NAME(symbol,typ) =>
            "NAME"
        | UNIT =>
            "UNIT"

end

