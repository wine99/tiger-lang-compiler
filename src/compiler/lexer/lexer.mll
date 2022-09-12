(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(* Do not distribute                                                      *)
(**************************************************************************)

{
  open Tigerparser.Parser  
  exception Error of string
  let error lexbuf msg =
    let position = Lexing.lexeme_start_p lexbuf in
    let err_str = Printf.sprintf "Lexing error in file %s at position %d:%d\n"
                  position.pos_fname position.pos_lnum (position.pos_cnum - position.pos_bol + 1)
                  ^ msg ^ "\n" in
    raise (Error err_str)
}

let whitespace = [' ' '\t' ]
let digits = ['0' - '9']+
let letter = ['a' - 'z' 'A' - 'Z']
let id = letter+ (letter | digit | '_')*

(* add more named regexps here *)

(* an entrypoint with a few starting regexps *)
rule token = parse
| whitespace          { token lexbuf }     (* skip blanks *)
| eof                 { EOF       }
| "/*"                { comment 0 lexbuf }
| ','                 { COMMA     }
| ';'                 { SEMICOLON }
| ":="                { ASSIGN    }
| "array"             { ARRAY }
| "if"                { IF }
| digits as i         { INT (int_of_string i) }
| id as i             { ID (i) }
| '"'                 { error lexbuf "string not impl" (* add string function *) }
| "{"                 { error lexbuf "record brace open not impl" (* add record function *) }

and comment level = parse
| eof    { error lexbuf "File ended in comment"                           }
| '\n'   { Lexing.new_line lexbuf ; comment level lexbuf                  }
| "/*"   { comment (level + 1) lexbuf                                     }
| "*/"   { if level = 0 then token lexbuf else comment (level - 1) lexbuf }
| _      { comment level lexbuf                                           }


(* default error handling *)
| _ as t              { error lexbuf ("Invalid character '" ^ (String.make 1 t) ^ "'") }
