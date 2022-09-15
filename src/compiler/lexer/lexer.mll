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

  let bigInt str lexbuf =
    if String.length str > 31 then
      error lexbuf "Integer too big for system."
    else
      INT (int_of_string str)

  let ascii_digit_range num lexbuf =
    if 0 <= num && num <= 255 then
      String.make 1 (Char.chr num)
    else
      error lexbuf "Number is not in the range of legal ASCII code."

  let is_allowed_char acc chr lexbuf =
    let num = Char.code chr in
    if 0 <= num && num <= 255 then
      acc ^ String.make 1 chr
    else
      error lexbuf "Illegal character"

}



let whitespace = [' ' '\t']
let digits = ['0' - '9']+
let small_letters = ['a' - 'z']
let big_letters = ['A' - 'Z']
let letter = small_letters | big_letters
let id = letter+ (letter | digits | '_')*
let ascii_digit = ['0' - '9']['0' - '9']['0' - '9']
let caret_letters = ['a' - 'g'] | ['k' - 'l'] | ['n' - 'z']

(** The main entrypoint for the lexer *)
rule token = parse
| whitespace          { token lexbuf                                                   }
| '\n'                { Lexing.new_line lexbuf ; token lexbuf                          }
| "\r\n"              { Lexing.new_line lexbuf ; token lexbuf                          }
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
| '['                 { LBRACK                                                         }
| ']'                 { RBRACK                                                         }
| ':'                 { COLON                                                          }
| '+'                 { PLUS                                                           }
| '-'                 { MINUS                                                          }
| '*'                 { TIMES                                                          }
| '/'                 { DIVIDE                                                         }
| '='                 { EQ                                                             }
| "<>"                { NEQ                                                            }
| '<'                 { LT                                                             }
| "<="                { LE                                                             }
| '>'                 { GT                                                             }
| ">="                { GE                                                             }
| '&'                 { AND                                                            }
| '|'                 { OR                                                             }
| '^'                 { CARET                                                          }
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
| digits              { bigInt (Lexing.lexeme lexbuf) lexbuf                           }
| id                  { ID (Lexing.lexeme lexbuf)                                      }
| '"'                 { str (Lexing.lexeme_start_p lexbuf) "" lexbuf                   }
| _ as t              { error lexbuf ("Invalid character '" ^ (String.make 1 t) ^ "'") }

and comment level = parse
| eof    { error lexbuf "File ended in comment"                           }
| '\n'   { Lexing.new_line lexbuf ; comment level lexbuf                  }
| "/*"   { comment (level + 1) lexbuf                                     }
| "*/"   { if level = 0 then token lexbuf else comment (level - 1) lexbuf }
| _      { comment level lexbuf                                           }

and str start_pos acc = parse
| '\\'   { let esc = escape_character lexbuf in str start_pos (acc ^ esc) lexbuf           }
| '"'    { lexbuf.lex_start_p <- start_pos ; STRING acc                                    }
| eof    { error lexbuf "Unclosed string"                                                  }
| _      { str start_pos (is_allowed_char acc (Lexing.lexeme_char lexbuf 0) lexbuf) lexbuf }



and escape_character = parse
| eof            { error lexbuf "Reached end of file in ecsape character." }
| ' '
| '\b'
| '\t'
| '\r'           { back_seq lexbuf } (* ignore whitespace in string *)
| '\n'           { Lexing.new_line lexbuf; back_seq lexbuf }
| '\\'           { "\\" }
| '"'            { "\"" }
| 'b'            { "\b" }
| 't'            { "\t" }
| 'n'            { "\n" }
| 'r'            { "\r" }
| "^h"           { "\b" }
| "^i"           { "\t" }
| "^j"           { "\n" }
| "^m"           { "\r" }
| '^'            { String.make 1 (Char.chr (caret_notation lexbuf))               }
| ascii_digit    { ascii_digit_range (int_of_string(Lexing.lexeme lexbuf)) lexbuf }
| _              { error lexbuf "Invalid escape character"                        }

and caret_notation = parse
| eof                { error lexbuf "Reached end of file in caret character." }
| '@'                { 0   }
| '['                { 27  }
| '\\'               { 28  }
| ']'                { 29  }
| '^'                { 30  }
| '_'                { 31  }
| '?'                { 127 }
| big_letters   as b { (Char.code (b)) - 64 }
| caret_letters as s { (Char.code (s)) - 96 }
| _                  { error lexbuf "Invalid escape character" }

and back_seq = parse
| eof  { error lexbuf "Reached end of file in string." }
| '\\' { ""                                            }
| '\n' { Lexing.new_line lexbuf ; back_seq lexbuf      }
| ' '  { back_seq lexbuf                               }
| '\b' { back_seq lexbuf                               }
| '\t' { back_seq lexbuf                               }
| '\r' { back_seq lexbuf                               }
