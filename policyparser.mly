%{
%}

%token <int> LIT
%token <string> VAR

%token ARROW
%token SUB
%token MUSTNOT
%token MUST
%token SHOULDNOT
%token SHOULD
%token SEMI
%token DOT
%token COLON
%token DASH
%token EOF

%start main
%type <Placepolicy.policy list> main
%type <Placepolicy.policy> policy
%type <Placepolicy.preference> pref
%type <string> filename
%%

main :
  policylist EOF { $1 }

policylist : 
  | policy SEMI policylist { $1 :: $3 }
  | policy SEMI            { [ $1 ] }

filename : 
  | VAR DOT VAR { $1 ^ "." ^ $3 } 
  | VAR { $1 }

policy : 
  | filename SUB VAR ARROW pref  { Placepolicy.MethodPolicy ($1,$3,$5) }
  | filename ARROW pref          { Placepolicy.FilePolicy ($1,$3) }
  | filename COLON LIT DASH LIT ARROW pref  { Placepolicy.LinePolicy ($1,$3,$5,$7) }

pref : 
  | MUST { Placepolicy.MustPreference }
  | MUSTNOT { Placepolicy.MustNotPreference }
  | SHOULD LIT { Placepolicy.ShouldPreference $2 }
  | SHOULDNOT LIT { Placepolicy.ShouldNotPreference $2 }

  
