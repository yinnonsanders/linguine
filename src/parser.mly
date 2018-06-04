
%{
open Ast
%}

(* Tokens *)

%token EOL

%token <int> NUM
%token <float> FLOAT
%token <string> ID
%token PLUS
%token MINUS
%token TIMES
%token CTIMES
%token COLON
%token LBRACK
%token RBRACK
%token LPAREN
%token RPAREN
%token TRANS
%token GETS
%token EQ
%token LEQ
%token AND
%token OR
%token NOT
%token COMMA
%token TAG
%token IS
%token MAT
%token VEC
%token DOT
%token NORM
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SKIP
%token PRINT
%token SEMI
%token INTTYP
%token FLOATTYP 
%token BOOLTYP

(* Precedences *)
%nonassoc COMMA
%left PLUS MINUS
%left TIMES
%left CTIMES


%left AND OR
%nonassoc DOT
%nonassoc NORM
%nonassoc NOT

%nonassoc SEMI
%nonassoc ELSE 

%left TRANS
%left COLON

(* After declaring associativity and precedence, we need to declare what
   the starting point is for parsing the language.  The following
   declaration says to start with a rule (defined below) named [prog].
   The declaration also says that parsing a [prog] will return an OCaml
   value of type [Ast.expr]. *)

%start main
%type <Ast.comm> main


(* The following %% ends the declarations section of the grammar definition. *)

%%
   
main:
  | e = comm; SEMI; EOL { e }
;
  
comm:
  | c1 = comm; SEMI; c2 = comm { Seq(c1, c2) }
  | TAG; x = ID; IS; e1 = ltyp { TagDecl(x, LTyp(e1)) }
  | SKIP { Skip } 
  | t = typ; x = ID; GETS; e1 = exp { Decl(t, x, e1) }
  | IF; LPAREN; b1 = bexp; RPAREN; THEN; c1 = comm; ELSE; c2 = comm { If(b1,c1,c2) }
  | PRINT; e = exp { Print(e) }
;

typ:
  | a = atyp { ATyp(a) }
  | b = btyp { BTyp(b) }
;

atyp:
  | FLOATTYP  { FloatTyp }
  | INTTYP    { IntTyp }
  | e = ltyp { LTyp(e) }
;

ltyp: 
  | VEC; i = NUM { VecTyp(i) }
  | MAT; i1 = NUM; TIMES; i2 = NUM { MatTyp(i1,i2) }
  | TAG; x = ID { TagTyp(x) }
  | x1 = ltyp; TRANS; x2 = ltyp { TransTyp(x1,x2) }
;

btyp:
  | BOOLTYP { BoolTyp }
;

exp:
  | a = aexp { Aexp(a) }
  | b = bexp { Bexp(b) }
;

aval: 
  | i = NUM { Num i }
  | f = FLOAT { Float f }
  | LBRACK; v = veclit; RBRACK { VecLit(v@[]) }
  | LBRACK; m = matlit; RBRACK { MatLit(m@[]) }
;

veclit:
  | f = FLOAT { f::[] }
  | v1 = veclit; COMMA; v2 = veclit { v1@v2@[] }
;

matlit:
  | LBRACK; v = veclit; RBRACK { [v] }
  | m1 = matlit; COMMA; m2 = matlit { m1@m2@[] }
;

aexp:
  | v = aval { Const v }  
  | x = ID { Var x }
  | e = aexp; COLON; t = ltyp { LExp(e, t) }
  | DOT; e1 = aexp; e2 = aexp { Dot(e1, e2) }
  | NORM; e = aexp { Norm(e) } (* Normie *)
  | e1 = aexp; PLUS; e2 = aexp { Plus(e1,e2) }
  | e1 = aexp; TIMES; e2 = aexp { Times(e1,e2) }
  | e1 = aexp; MINUS; e2 = aexp { Minus(e1,e2) }
  | e1 = aexp; CTIMES; e2 = aexp { CTimes(e1,e2) }
;

bexp:
  | TRUE { True }
  | FALSE { False }
  | e1 = aexp; EQ; e2 = aexp { Eq(e1,e2) }
  | e1 = aexp; LEQ; e2 = aexp { Leq(e1,e2) }
  | e1 = bexp; OR; e2 = bexp { Or(e1,e2) }
  | e1 = bexp; AND; e2 = bexp { And(e1,e2) }
  | NOT; e1 = bexp;{ Not(e1) }
;

%%