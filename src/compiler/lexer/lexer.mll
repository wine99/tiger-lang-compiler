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
let id = letter+ (letter | digits | '_')*

(* add more named regexps here *)

(* an entrypoint with a few starting regexps *)
rule token = parse
| whitespace          { token lexbuf                                                   }
| eof                 { EOF                                                            }
| "/*"                { comment 0 lexbuf                                               }
| '.'                 { DOT                                                            }
| ','                 { COMMA                                                          }
| ';'                 { SEMICOLON                                                      }
| ":="                { ASSIGN                                                         }
| '('                 { LPAREN                                                         }
| ')'                 { RPAREN                                                         }
| '{'                 { LBRACE                                                         }
| '}'                 { RBRACE                                                         }
| '['                 { LBRACKET                                                       }
| ']'                 { RBRACKET                                                       }
| ':'                 { COLON                                                          }
| '+'                 { PLUS                                                           }
| '-'                 { MINUS                                                          }
| '*'                 { TIMES                                                          }
| '/'                 { DIV                                                            }
| '='                 { EQ                                                             }
| "<>"                { NEQ                                                            }
| '<'                 { LT                                                             }
| "<="                { LEQ                                                            }
| '>'                 { GT                                                             }
| ">="                { GEQ                                                            }
| '&'                 { AMPERSAND                                                      }
| '|'                 { PIPE                                                           }
| "array"             { ARRAY                                                          }
| "if"                { IF                                                             }
| "while"             { WHILE                                                          }
| "for"               { FOR                                                            }
| "to"                { TO                                                             }
| "break"             { BREAK                                                          }
| "let"               { LET                                                            }
| "in"                { IN                                                             }
| "end"               { END                                                            }
| "function"          { FUNCTION                                                       }
| "var"               { VAR                                                            }
| "type"              { TYPE                                                           }
| "then"              { THEN                                                           }
| "else"              { ELSE                                                           }
| "do"                { DO                                                             }
| "of"                { OF                                                             }
| "nil"               { NIL                                                            }
| digits as i         { INT (int_of_string i)                                          }
| id as i             { ID (i)                                                         }
| '"'                 { string "\"" lexbuf                                             }
| _ as t              { error lexbuf ("Invalid character '" ^ (String.make 1 t) ^ "'") }

and comment level = parse
| eof    { error lexbuf "File ended in comment"                           }
| '\n'   { Lexing.new_line lexbuf ; comment level lexbuf                  }
| "/*"   { comment (level + 1) lexbuf                                     }
| "*/"   { if level = 0 then token lexbuf else comment (level - 1) lexbuf }
| _      { comment level lexbuf                                           }

and string acc = parse
| '\'  { let esc = escape_character lexbuf in string (acc ^ esc) } 
| '"'  { STRING (acc ^ "\"")                                     }
| eof  { error lexbuf "Unclosed string"                          }
| c    { string (acc ^ c)                                        }

and escape = parse
| '\' { "\\" }
| 'n' { "\n" }
| 't' { "\t" }
| 'r' { "\r" }
| '"' { "\"" }
| 'b' { "\b" }
| c   { error lexbuf "Invalid escape character" }