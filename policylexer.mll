{
  open Policyparser
  exception Eof
}
rule token = parse
    [' ' '\t' '\n'] {token lexbuf}
  | ['0'-'9']+ as lxm {LIT(int_of_string lxm)}
  | "."          {DOT}
  | "->"         {ARROW}
  | "-"          {DASH}
  | "::"         {SUB}
  | ":"          {COLON}
  | "must not"   {MUSTNOT}
  | "must"       {MUST}
  | "should not" {SHOULDNOT}
  | "should"     {SHOULD}
  | ";"          {SEMI}
  | ['a'-'z''A'-'Z']+['a'-'z''A'-'Z''0'-'9']* as lxm {VAR(lxm)}
  | eof   {EOF}

