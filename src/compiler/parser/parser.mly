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
%nonassoc SEMICOLON
%right ASSIGN
%right DO
%nonassoc EQ NEQ LT LE GT GE
%left PLUS MINUS
%left TIMES DIVIDE
%nonassoc UMINUS
%right CARET

%start <Tigercommon.Absyn.exp> program
(* Observe that we need to use fully qualified types for the start symbol *)

%%
(* Expressions *)
exp_base:
| v = var    { VarExp v    }
| NIL        { NilExp      }
| i = INT    { IntExp i    }
| s = STRING { StringExp s }
| func = id LPAREN args = separated_list(COMMA, exp) RPAREN { CallExp { func ; args } }
| MINUS right = exp %prec UMINUS { let left = (IntExp 0) ^! $startpos  in let oper = MinusOp in OpExp { left ; oper ; right } } (* Unary minus *)
| left = exp oper = oper right = exp { OpExp { left ; oper ; right } }
| typ = id LBRACE fields = separated_list(SEMICOLON, record_field) RBRACE { RecordExp { fields ; typ } }
| head = exp SEMICOLON tail = exp { SeqExp ([head ; tail]) }
| var = var ASSIGN exp = exp { AssignExp { var ; exp } }
// | IF test = exp THEN e1 = exp_base ELSE e2 = exp_base { let thn = e1 ^! $startpos in let els = Some (e2 ^! $startpos) in IfExp { test ; thn ; els } }
| WHILE test = exp DO body = exp { WhileExp { test ; body } }

// unmatched_if_then_exp:
// | IF test = exp THEN thn = exp { let els = None in IfExp { test ; thn ; els } }
// | IF test = exp THEN e1 = exp_base ELSE e2 = unmatched_if_then_exp { let thn = e1 ^! $startpos in let els = Some (e2 ^! $startpos) in IfExp { test ; thn ; els } }

record_field:
| symbol = id EQ exp = exp { (symbol, exp) }

id:
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

(* Top-level *)
program: e = exp EOF { e }

exp:
| e = exp_base  { e ^! $startpos }
// | e = unmatched_if_then_exp { e ^! $startpos }

(* Variables *)
var_base:
| id = id                       { SimpleVar    id      }
| v = var DOT id = id           { FieldVar     (v, id) }
| v = var LBRACK e = exp RBRACK { SubscriptVar (v, e)  }

var:
| v = var_base { v ^@ $startpos }
