(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(* Do not distribute                                                      *)
(**************************************************************************)

%{
  open Tigercommon.Absyn
  open ParserAux
  open Tigercommon.Symbol
%}

%token EOF
%token <string> ID
%token <int> INT
%token <string> STRING
%token COMMA COLON SEMICOLON
%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token DOT PLUS MINUS TIMES DIVIDE EQ NEQ LT LE GT GE
%token AND OR ASSIGN ARRAY IF THEN ELSE WHILE FOR TO DO
%token LET IN END OF BREAK NIL FUNCTION VAR TYPE CARET

(* Operator Precedence & Associativity *)
%right ASSIGN
%right THEN
%right ELSE
%right DO
%right OF
%nonassoc EQ NEQ LT LE GT GE
%left PLUS MINUS
%left TIMES DIVIDE
%nonassoc UMINUS
%right CARET

%start <Tigercommon.Absyn.exp> program
(* Observe that we need to use fully qualified types for the start symbol *)

%%
(* Expressions *)
// TODO what does escape do
exp_base:
| v = var                                                                     { VarExp v                                                                     }
| i = INT                                                                     { IntExp i                                                                     }
| s = STRING                                                                  { StringExp s                                                                  }
| NIL                                                                         { NilExp                                                                       }
| BREAK                                                                       { BreakExp                                                                     }
| func = sym_id LPAREN args = separated_list(COMMA, exp) RPAREN               { CallExp   { func ; args                                                    } }
| MINUS right = exp %prec UMINUS                 (* Unary minus *)            { OpExp     { left = (IntExp 0) ^! $startpos(right) ; oper = MinusOp ; right } }
| left = exp oper = oper right = exp                                          { OpExp     { left ; oper ; right                                            } }
| typ = sym_id LBRACE fields = separated_list(SEMICOLON, record_field) RBRACE { RecordExp { fields ; typ                                                   } }
| LPAREN seq = separated_list(SEMICOLON, exp) RPAREN                          { SeqExp    seq                                                                }
| var = var ASSIGN exp = exp                                                  { AssignExp { var ; exp                                                      } }
| IF test = exp THEN thn = exp ELSE els = exp                                 { IfExp     { test ; thn ; els = Some els                                    } }
| IF test = exp THEN thn = exp                                                { IfExp     { test ; thn ; els = None                                        } }
| WHILE test = exp DO body = exp                                              { WhileExp  { test ; body                                                    } }
| FOR var = sym_id ASSIGN lo = exp TO hi = exp DO body = exp                  { ForExp    { var ; escape = ref true ; lo ; hi ; body                       } }
// TODO decl is not seperated by SEMECOLON
| LET decls = separated_nonempty_list(SEMICOLON, decl) IN body = expseq END   { LetExp    { decls ; body                                                   } }
| typ = sym_id size = subscript_exp OF init = exp                             { ArrayExp  { typ; size ; init                                               } }

expseq:
| seq = separated_nonempty_list(SEMICOLON, exp) { (SeqExp seq) ^! $startpos}


decl:
| fundecldata = list(fundecldata)                            { FunctionDec fundecldata                                             }
| VAR name = sym_id typ = opt_type_ascript ASSIGN init = exp { VarDec { name ; escape = ref true ; typ ; init ; pos = $startpos  } }
| TYPE tydecldata = list(tydecldata)                         { TypeDec tydecldata                                                  }


fundecldata:
| FUNCTION name = sym_id LPAREN params = fielddata RPAREN result = opt_type_ascript EQ body = exp { Fdecl { name ; params ; result ; body ; pos = $startpos } }


fielddata:
| l = separated_list(COMMA, one_fielddata) { l }


tydecldata:
| name = sym_id EQ ty = base_typ { Tdecl { name ; ty ; pos = $startpos } }


base_typ:
| t = sym_id                  { NameTy  (t, $startpos) }
| LBRACE t = fielddata RBRACE { RecordTy t             }
| ARRAY OF t = sym_id         { ArrayTy (t, $startpos) }


(* Top-level *)
program: e = exp EOF { e }

exp:
| e = exp_base  { e ^! $startpos }

(* Variables *)
var_base:
| id = sym_id               { SimpleVar    id      } // Solve this shift reduce conflict w subscript_exp
| v = var DOT id = sym_id   { FieldVar     (v, id) }
| v = var e = subscript_exp { SubscriptVar (v, e ) }

subscript_exp:
| LBRACK e = exp RBRACK { e }

var:
| v = var_base { v ^@ $startpos }

record_field:
| symbol = sym_id EQ exp = exp { (symbol, exp) }

sym_id:
| id = ID { symbol id }

%inline oper:
| EQ     { EqOp       }
| NEQ    { NeqOp      }
| LT     { LtOp       }
| LE     { LeOp       }
| GT     { GtOp       }
| GE     { GeOp       }
| PLUS   { PlusOp     }
| MINUS  { MinusOp    }
| TIMES  { TimesOp    }
| DIVIDE { DivideOp   }
| CARET  { ExponentOp }

type_id:
| sym = sym_id { (sym, $startpos(sym)) }


opt_type_ascript:
| ota = option(preceded(COLON, type_id)) { ota }


one_fielddata:
| name = sym_id COLON typ = type_id { Field { name ; escape = ref true ; typ ; pos = $startpos } }
