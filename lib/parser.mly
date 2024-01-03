%token <float> FLOAT
%token <int> INT
%token <string> ID
%token <string> UPPER_ID
%token <string> STRING
%token EOF
%token NULL SIZE_OF RETURN
%token EQ, GE, GT, LE, LT, NE
%token AND, OR
%token ARROW
%token IF, THEN, ELSE
%token PLUS MINUS TIMES DIV REM AMP CARET
%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK DOT
%token LBRACEPIPE PIPERBRACE
%token EQUALS SEMICOLON COMMA HASH COLON PIPE
%token MATCH WITH
%token TRUE FALSE
%token <char> CHAR
%token LET TYPE EXTERN IMPLICIT_EXTERN ASSERT
%token UNSAFE_CAST

%left EQUALS
%right OR
%right AND
%right ARROW
%left EQ, GE, GT, LE, LT, NE
%left PLUS MINUS
%left TIMES DIV REM
%nonassoc AMP STAR
%left DOT LBRACK
%left CARET
%left LPAREN

%start <Ast.toplevel list> prog
%%

prog:
  | list(toplevel); EOF
    { $1 }
    

name:
  | i = ID
    { i }

atom:
  | LPAREN; RPAREN
    { `Unit }
  | f = FLOAT
    { `Float f }
  | i = INT
    { `Int i }
  | i = name
    { `Var i }
  | s = STRING
    { `String s }
  | c = CHAR
    { `Char c }
  | NULL
    { `Null }
  | TRUE
    { `Bool true }
  | FALSE
    { `Bool false }

struct_name:
  | HASH; n = name
    { n }

type_expr_wrapped:
  | LPAREN; a = type_expr; COMMA; l = separated_list(COMMA, type_expr); RPAREN
    { `Tuple (a :: l) }
  | LPAREN; a = type_expr; RPAREN
    { a }

type_expr_no_whitespace:
  | n = name
    { `Named n }
  | type_expr_wrapped
    { $1 }

type_expr:
  | n = name; LPAREN; l = separated_nonempty_list(COMMA, type_expr); RPAREN
    { `Named_args (n, l) }
  | a = type_expr; ARROW; b = type_expr
    { `Function (a, b) }
  | AMP; t = type_expr
    { `Pointer t }
  | t = type_expr_no_whitespace
    { t }

pattern_wrapped:
  | LPAREN; p = pattern; COMMA; l = separated_list(COMMA, pattern); RPAREN
    { `Tuple (p :: l) }
  | LPAREN; p = pattern; RPAREN
    { p }
  | LPAREN; p = pattern; COLON; t = type_expr; RPAREN
    { `Typed (p, t) }

pattern_no_whitespace:
  | a = atom
    { (a :> Ast.pattern) }
  | pattern_wrapped
    { $1 }
  | n = struct_name; LBRACE; l = separated_nonempty_list(SEMICOLON, pattern_struct_element); RBRACE
    { `Struct (n, l) }
  | n = struct_name; LBRACE; RBRACE 
    { `Struct (n, []) }
  | AMP; p = pattern_no_whitespace
    { `Ref p }

pattern:
  | p = pattern_no_whitespace
    { p }
  | i = UPPER_ID; p = option(pattern_wrapped)
    { `Enum (i, p) }

pattern_struct_rhs:
  | COLON; p = pattern
    { p }

pattern_struct_element:
  | i = ID; p = option(pattern_struct_rhs)
    { (i, p) }

var_decl:
  | n = name; COLON; t = type_expr
    { `Typed (n, t) }
  | n = name
    { `Untyped n }

let_:
  | LET; p = pattern; COLON; t = type_expr; EQUALS; e = expr
    { `Let (p, `Typed (e, t)) }
  | LET; p = pattern; COLON; EQUALS; e = expr
    { `Let (p, e) }

let_fn:
  | LET; n = name; LPAREN; RPAREN; COLON; t = type_expr; EQUALS; e = expr
    { `Let_fn (n, [ `Typed ("1", `Unit) ], `Typed (e, t)) }
  | LET; n = name; LPAREN; RPAREN; COLON; EQUALS; e = expr
    { `Let_fn (n, [ `Typed ("1", `Unit) ], e) }
  | LET; n = name; LPAREN; l = separated_nonempty_list(COMMA, var_decl); RPAREN; COLON; t = type_expr; EQUALS; e = expr
    { `Let_fn (n, l, `Typed (e, t)) }
  | LET; n = name; LPAREN; l = separated_nonempty_list(COMMA, var_decl); RPAREN; COLON; EQUALS; e = expr
    { `Let_fn (n, l, e) }

expr_wrapped:
  | LPAREN; e = expr; RPAREN
    { e }
  | LPAREN; e = expr; COLON; t = type_expr; RPAREN
    { `Typed (e, t) }
  | LPAREN; e = expr; COMMA; l = separated_list(COMMA, expr); RPAREN
    { `Tuple (e :: l) }

expr_no_whitespace:
  | a = atom
    { (a :> Ast.expr) }
  | expr_wrapped
    { $1 }
  | LBRACE; e = compound_expr; RBRACE
    { e }

expr_ops:
  | e = expr_no_whitespace
    { e }
  | SIZE_OF; LBRACK; b = type_expr; RBRACK
    { `Size_of (`Type b) }
  | SIZE_OF; LPAREN; b = expr; RPAREN
    { `Size_of (`Expr b) }
  | ASSERT; LPAREN; b = expr; RPAREN
    { `Assert b }
  | RETURN; LPAREN; b = expr; RPAREN
    { `Return b }
  | UNSAFE_CAST; LPAREN; b = expr; RPAREN
    { `Unsafe_cast b }
  | a = expr_ops; LPAREN; RPAREN
    { `Apply (a, `Unit) }
  | a = expr_ops; LPAREN; b = expr; RPAREN
    { `Apply (a, b) }
  | a = expr_ops; LPAREN; b = expr; COMMA; l = separated_nonempty_list(COMMA, expr); RPAREN
    { `Apply (a, `Tuple (b :: l)) }
  | AMP; e = expr_ops
    { `Ref e }
  | e = expr_ops; CARET
    { `Deref e }
  | TIMES; e = expr_ops %prec STAR
    { `Deref e }
  | o = unop; e = expr_ops %prec STAR
    { `Pref_op (o, e) }
  | a = expr_ops; o = binop; b = expr_ops
    { `Inf_op (o, a, b) }
  | e = expr_ops; DOT; i = INT
    { `Tuple_access (e, i) }
  | e = expr_ops; DOT; i = ID
    { `Field_access (e, i) }
  | e = expr_ops; LBRACK; i = expr; RBRACK
    { `Index (e, i) }
  | i = UPPER_ID
    { `Enum i }
  | a = expr_ops; EQUALS; b = expr_ops
    { `Assign (a, b) }
%inline unop:
  | MINUS { `Minus }
%inline binop:
  | EQ { `Eq }
  | NE { `Ne }
  | GE { `Ge }
  | GT { `Gt }
  | LE { `Le }
  | LT { `Lt }
  | PLUS { `Add }
  | MINUS { `Sub }
  | TIMES { `Mul }
  | DIV { `Div }
  | REM { `Rem }
  | AND { `And }
  | OR { `Or }

match_each:
  | p = pattern; ARROW; e = expr_ops
    { (p, e) }

expr_no_let:
  | e = expr_ops
    { e }
  | n = struct_name; LBRACE; l = separated_nonempty_list(SEMICOLON, expr_struct_element);
    RBRACE
    { `Struct (n, l) }
  | LBRACEPIPE; l = separated_nonempty_list(SEMICOLON, expr); PIPERBRACE
    { `Array_lit l }
  | n = struct_name; LBRACE; RBRACE 
    { `Struct (n, []) }
  | IF; a = expr; THEN; b = expr; ELSE; c = expr
    { `If (a, b, c) }
  | MATCH; e = expr; WITH; PIPE; l = separated_nonempty_list(PIPE, match_each)
    { `Match (e, l) }

let_part:
  | LET; p = pattern; COLON; t = type_expr; EQUALS; e = expr
    { (p, `Typed (e, t)) }
  | LET; p = pattern; COLON; EQUALS; e = expr
    { (p, e) }
 

expr:
  | e = expr_no_let
    { e }
  | t = let_part; SEMICOLON; r = expr
    { `Let (fst t, snd t, r) }

compound_inner:
  | e = expr_no_let
    { `Expr e }
  | IF; a = expr; THEN; b = expr
    { `Expr (`If (a, `Let (`Var "_", b, `Unit), `Unit)) }
  | t = let_part
    { `Let t }

compound_expr:
  | separated_list(SEMICOLON, compound_inner)
    { `Compound $1 }

expr_struct_inner:
  | COLON; e = expr
    { e }

expr_struct_element:
  | i = ID; e = option(expr_struct_inner)
    { (i, e) }

type_decl_name:
  | n = name; LPAREN; l = separated_nonempty_list(COMMA, name); RPAREN
    { (n, l) }
  | n = name
    { (n, []) }

type_decl_enum_each:
  | n = UPPER_ID; t = option(type_expr_wrapped)
    { (n, t) }

type_decl_struct_each:
  | n = ID; COLON; t = type_expr
    { (n, t) }

type_decl:
  | t = type_expr_no_whitespace
    { `Alias t }
  | PIPE; l = separated_list(PIPE, type_decl_enum_each)
    { `Enum l }
  | LBRACE; l = separated_list(SEMICOLON, type_decl_struct_each); RBRACE
    { `Struct l }


let_type:
  | TYPE; n = type_decl_name; COLON; EQUALS; t = type_decl
    { `Let_type (n, t) }

extern:
  | EXTERN; n = name; COLON; t = type_expr; EQUALS; s = STRING
    { `Extern (n, t, s) }

implicit_extern:
  | IMPLICIT_EXTERN; n = name; COLON; t = type_expr; EQUALS; s = STRING
    { `Implicit_extern (n, t, s) }

toplevel:
  | let_
    { $1 }
  | let_fn
    { $1 }
  | let_type
    { $1 }
  | extern
    { $1 }
  | implicit_extern
    { $1 }
