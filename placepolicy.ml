(* this file will process the placement policy as 
   loaded and understood by the policy parser/lexer *)

type preference = 
  | MustPreference
  | MustNotPreference
  | ShouldPreference of int
  | ShouldNotPreference of int

type policy = 
  | MethodPolicy of string * string * preference
  | FilePolicy of string * preference
  | LinePolicy of string * int * int * preference

let preference_to_string p = 
  match p with 
    | MustPreference -> "must"
    | MustNotPreference -> "must not"
    | ShouldPreference n -> "should(" ^ (string_of_int n) ^ ")"
    | ShouldNotPreference n -> "should not(" ^ (string_of_int n) ^ ")"

let policy_to_string p =
  match p with
    | MethodPolicy (f,m,pf) -> f ^ "::" ^ m ^ " -> " ^ (preference_to_string pf)
    | FilePolicy (f,pf) -> f ^ " -> " ^ (preference_to_string pf)
    | LinePolicy (f,s,e,pf) -> f ^ ":" ^ (string_of_int s) ^ "-" ^ (string_of_int e) ^ " -> " ^ (preference_to_string pf)


let position_matches_policy pos p = 
  match p with
    | MethodPolicy (f,m,pf) -> false
    | FilePolicy (f,pf) -> 
	let reg = Str.regexp (String.escaped f)  in
	  if (Str.string_match reg pos 0) then
	    true
	  else
	    false
    | LinePolicy (f,s,e,pf) ->
	(* TODO: more here *)
	let reg = Str.regexp (String.escaped f)  in
	  if (Str.string_match reg pos 0) then
	    true
	  else
	    false

let preference_for_policy p =
  match p with
    | MethodPolicy (f,m,pf) -> pf
    | FilePolicy (f,pf) -> pf
    | LinePolicy (f,s,e,pf) -> pf

let policy = ref []

let get_preference_for_pos pos = 
  try 
    Some (preference_for_policy (List.find (position_matches_policy pos) (!policy)))
  with Not_found -> None
