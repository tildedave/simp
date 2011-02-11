/* File simp.mly */
%{
open Simp
%}

%token <int> LIT
%token <string> VAR
%token PLUS

%token ASSIGN
%token IF
%token THEN
%token ELSE
%token END
%token DO
%token WHILE
%token SEMI
%token SKIP
%token EOF

%left ASSIGN
%start main
%type <Simp.command> main
%%
main:
    comlist EOF { $1 }

comlist :
    com   { $1 }
  | com SEMI comlist {Simp.Seq($1,$3)}

com :
    SKIP
           {Simp.Skip}
  | VAR ASSIGN exp 
           {Simp.Assign (Simp.EVar $1,$3)}
  | IF exp THEN comlist ELSE comlist END
           {Simp.If ($2,$4,$6)}
  | WHILE exp DO comlist END
           {Simp.While ($2,$4)}

exp : 
  | LIT
           {Simp.ELit $1}
  | VAR
           {Simp.EVar $1}
  | exp PLUS exp
           {Simp.EAdd ($1,$3)}
