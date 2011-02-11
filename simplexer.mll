{
  open Simpparser
  exception Eof 
}
rule token = parse
    [' ' '\t' '\n'] {token lexbuf}
  | ['0'-'9']+ as lxm {LIT(int_of_string lxm)}
  | "+"         {PLUS}
  | ":="        {ASSIGN}
  | "if"        {IF}
  | "then"      {THEN}
  | "else"      {ELSE}
  | "end"       {END}
  | "do"        {DO}
  | "while"     {WHILE}
  | ";"         {SEMI}
  | "skip"      {SKIP}
  | ['a'-'z''A'-'Z']+['a'-'z''A'-'Z''0'-'9']* as lxm {VAR(lxm)}
  | eof   {EOF}
