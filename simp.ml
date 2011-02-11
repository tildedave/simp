let prune = ref true
let output_declassifiers = ref false

type exp = 
  | ELit of int
  | EVar of string
  | EAdd of exp * exp

type command = 
  | Skip
  | Seq of (command * command)
  | Assign of (exp * exp)
  | If of (exp * command * command) 
  | While of (exp * command)

let rec exp_to_string e = 
    match e with
      | ELit n -> string_of_int n
      | EVar v -> v
      | EAdd (e1,e2) -> (exp_to_string e1) ^ " + " ^ (exp_to_string e2)

let command_to_string c = 
  let rec command_to_string_helper c pre =
    match c with
      | Skip -> "skip"
      | Seq (c1,c2) -> (command_to_string_helper c1 pre) ^ ";" ^ (command_to_string_helper c2 pre)
      | Assign (e1,e2) -> (exp_to_string e1) ^ " := " ^ (exp_to_string e2)
      | If (e,c1,c2) -> 
	  let newpre = (pre ^ "   ") in
	  "if " ^ (exp_to_string e) ^ " then\n" ^ 
	    newpre ^ (command_to_string_helper c1 newpre) ^ 
	    "\n" ^ pre ^ "else\n" ^ 
	    newpre ^ (command_to_string_helper c2 newpre) ^ "\n" ^ pre ^ "end"
      | While (e,c) -> 
	  "while " ^ (exp_to_string e) ^ " do\n" ^ 
	    pre ^ (command_to_string_helper c (pre ^ "  "))
  in
    command_to_string_helper c ""


let rec is_legal_command c = 
  match c with 
  | Skip -> Skip
  | Seq (c1,c2) -> Seq(is_legal_command c1,is_legal_command c2)
  | Assign (EVar v,le) -> Assign (EVar v,le)
  | Assign (_,_) -> raise (Failure ("command " ^ (command_to_string c) ^ " is not a legal command"))
  | If (e,c1,c2) -> If(e,is_legal_command c1,is_legal_command c2)
  | While (e,c) -> While(e,is_legal_command c)

type lexp_tag = 
    [`UniqId of string | `Weight of int | `Incoming | `Outgoing | `Position of string | `ExpStr of string | `NoDecl | `Procedure of int ]

type lvar = 
  | PCLVar of int 
  | ExpLVar of string
  | VarLVar of string

type lexp = 
  | Join of lexp * lexp 
  | LVar of lvar * lexp_tag list
  | Label of int

type cons = Leq of lexp * lexp

module LatticeGraph = 
  struct
    include Graph.Persistent.Digraph.Concrete(
      struct type t = (string * int) 
	     let compare (s1,id1) (s2,id2) = compare id1 id2 
	     let hash = Hashtbl.hash
	     let equal = (=)
      end)

    let find_uniq_vertex_with_criteria f g = fold_vertex (fun v -> fun candidate -> 
							   if (f g v) then
							     match candidate with
								 None -> Some v
							       | Some _ -> raise (Failure "more than one candidate")
							   else
							     candidate) g None
							   

    (*let bottom = find_uniq_vertex_with_criteria (fun g -> fun v -> in_degree g v = 0)*)

    let vertex_for_id id = find_uniq_vertex_with_criteria (fun g -> fun (s,id') -> id = id')

    let is_bottom g id = 
      match (vertex_for_id id g) with
	  None -> raise (Failure "couldn't find id") 
	| Some v -> (in_degree g v) = 0

    (*let find_max_id g = fold_vertex (fun (s,id) -> fun candidate -> if id > candidate then id else candidate) g (-1) *)

    (* coded stupidly, but lattice will be small *)
    let get_incomparable_pairs g = 
      let table = Hashtbl.create (nb_vertex g) in
	iter_vertex 
	  (fun v1 -> 
	     iter_vertex 
	       (fun v2 -> 
		  (* if v1 doesn't have an edge to v2, v1 </= v2 *)
		  if not (mem_edge g v1 v2) && not (v1 = v2) then
		    if (Hashtbl.mem table v1) then
		      Hashtbl.replace table v1 (v2 :: (Hashtbl.find table v1))
		    else
		      Hashtbl.add table v1 [v2])
	       g)
	  g;
	Hashtbl.fold (fun key -> fun value -> fun soFar -> (key,value) :: soFar) table []

    let string_of_incomparable_pairs g = 
      List.fold_left (fun str -> fun ((s1,id1),vl) -> Printf.sprintf ("incomparable: %s(%s,%d) with %s\n") str s1 id1 (String.concat ";" (List.map (fun (s1,id1) -> "(" ^ s1 ^ "," ^ (string_of_int id1) ^ ")") vl))) "" (get_incomparable_pairs g) 


  end

let defaultLattice = 
  let bottomVertex = "BOTTOM",0 and
      topVertex = "TOP", 1 in
    LatticeGraph.add_edge (LatticeGraph.add_vertex (LatticeGraph.add_vertex LatticeGraph.empty bottomVertex) topVertex) bottomVertex topVertex

let bottom = Label 0
let top = Label 1

let lvar_to_string v = 
  match v with
    | VarLVar e -> e
    | ExpLVar e -> e
    | PCLVar n -> "pc_" ^ (string_of_int n)

let rec atom_to_string a = 
  match a with
    | LVar (v,_) -> lvar_to_string v
    | Label n -> ("LATTICE " ^ (string_of_int n))
    | Join (_,_) -> raise (Failure "can't convert non-atom to string")

let tag_to_string t =
  match t with
    | `Incoming -> "incoming"
    | `Outgoing -> "outgoing"
    | `UniqId str -> "id=" ^ str
    | `Position pos -> "pos=" ^ pos
    | `ExpStr str -> "expstr=" ^ str
    | `NoDecl -> "nodecl"
    | `Weight n -> "weight=" ^ (string_of_int n)
    | `Procedure n -> "procedure=" ^ (string_of_int n)

let rec lexp_to_string le = 
  match le with
    | LVar (v,_) -> lvar_to_string v
    | Label n -> if n = 0 then "BOTTOM" else "TOP"
    | Join (le,le') -> (lexp_to_string le) ^ " ; " ^ (lexp_to_string le')

let cons_to_string c =
  match c with 
    | Leq (le,a) -> (lexp_to_string le) ^ " <= " ^ (lexp_to_string a)

let command_to_constraints c = 
  let pc_to_lvar (pcnum: int) = LVar (PCLVar pcnum,[]) in
  let variable_for_exp e en = 
    LVar (ExpLVar ((string_of_int en) ^ "(" ^ (exp_to_string e) ^ ")"),
	  [`ExpStr (exp_to_string e); `UniqId (string_of_int en)]) in
  let var_to_constraints e evar isread = 
    match e with
      | EVar "l" -> 
	  if (isread == true) then 
	    [Leq (bottom,evar)]
	  else
	    [Leq (evar,bottom)]
      | EVar "h" ->
	  if (isread == true) then
	    [Leq (top,evar)]
	  else
	    [Leq (evar,top)]
      | EVar "h2" ->
	  if (isread == true) then
	    [Leq (top,evar)]
	  else
	    [Leq (evar,top)]
      | EVar "h3" ->
	  if (isread == true) then
	    [Leq (top,evar)]
	  else
	    [Leq (evar,top)]
      | EVar n -> 
	  if (isread == true) then
	    [Leq (LVar (VarLVar n,[]),evar)]
	  else
	    [Leq (evar,LVar (VarLVar n,[]))]
      | _ -> raise (Failure "can't convert non-expression variable to constraints")
  in
  let rec exp_to_constraints e en =
    (* TODO: clean this up so that expression numbers are encapsulated
     * by a reference and a function (like the pc is now) -- won't even 
     * need to pass it around any more *)
    let evar = variable_for_exp e (en + 1) in
      match e with 
	| EAdd (e1,e2) ->
	    let (en',e1Cons) = exp_to_constraints e1 en in
	    let (en'',e2Cons) = exp_to_constraints e2 en' in
	    let evar = variable_for_exp e (en'' + 1) in
	      (en'' + 1,Leq (variable_for_exp e1 en',evar) ::
		 Leq (variable_for_exp e2 en'',evar) :: (e1Cons @ e2Cons))
	| ELit n -> (en + 1,[Leq (bottom,evar)])
	| EVar n -> (en + 1,var_to_constraints (EVar n) evar true)
  in
  let pcref = ref 0 in
  let get_next_pcnum () = (pcref := (!pcref) + 1); !pcref in
  let rec command_to_constraints_helper pcnum expnum c =
    match c with 
      | Skip -> (expnum,[])
      | Seq (c1,c2) ->
	  let (en,c1Cons) = command_to_constraints_helper pcnum expnum c1 in
	  let (en',c2Cons) = command_to_constraints_helper pcnum en c2 in  
	    (en',c1Cons @ c2Cons)
      | Assign (EVar v,e2) -> 
	  let lhsVar = LVar (VarLVar v,[]) in
	  let e1Cons = var_to_constraints (EVar v) lhsVar false in
	  let (en',e2Cons) = exp_to_constraints e2 expnum in
	  let assignCons = Leq (variable_for_exp e2 en',lhsVar) and
	      pcCons = Leq (pc_to_lvar pcnum, lhsVar)
	  in
	    (en',assignCons :: pcCons :: (e1Cons @ e2Cons))
      | Assign (_,_) -> raise (Failure "lhs of assign command is not variable")
      | If (e,c1,c2) ->
	  let (en,eCons) = exp_to_constraints e expnum in
	  let bodyPC = get_next_pcnum () in
	  let (en',c1Cons) = command_to_constraints_helper bodyPC en c1 in
	  let (en'',c2Cons) = command_to_constraints_helper bodyPC en' c2
	  in
	    (en'',eCons @ c1Cons @ c2Cons @ [Leq (Join (pc_to_lvar pcnum,
							 variable_for_exp e en),
						pc_to_lvar bodyPC)])
      | While (e,c) ->
	  let (en,eCons) = exp_to_constraints e expnum in
	  let bodyPC = get_next_pcnum () in
	  let (en',cCons) = command_to_constraints_helper bodyPC en c 
	  in
	    (en',eCons @ cCons @ [Leq (Join (pc_to_lvar pcnum,
					      variable_for_exp e en),
				       pc_to_lvar bodyPC)]) in
  let (_,cons) = command_to_constraints_helper 0 0 c and
      (* due to lack of polymorphic recursion (I think), type system can't
	 determine if RHS of returned set is only Label/LVar.  the following
	 function tells it so *)
      verify_rhs = List.fold_left (fun l -> fun c -> 
				     match c with 
				       | Leq (a,Label n) -> Leq (a,Label n) :: l
				       | Leq (a,LVar (v,t)) ->  Leq (a,LVar (v,t)) :: l
				       | _ -> raise (Failure "returned set has non-definite constraint")) [] in
    verify_rhs cons

let rec fold_left_lexp f i lexp =
  match lexp with 
    | Join (a,le) -> fold_left_lexp f (f i a) le
    | LVar (v,t) -> (f i (LVar (v,t)))
    | Label n -> (f i (Label n))

let rec fold_right_lexp f lexp i =
  match lexp with 
    | Join (a,le) -> f a (fold_right_lexp f le i)
    | LVar (v,t) -> (f (LVar (v,t)) i)
    | Label n -> (f (Label n) i)

module LexpSet = Set.Make(struct type t = lexp let compare = compare end)

let atoms_in_lexp lexp = fold_left_lexp (fun l -> fun a -> LexpSet.add a l) LexpSet.empty lexp

let atoms_in_cons c =
  match c with
    | Leq (le,a) -> LexpSet.add a (atoms_in_lexp le)

let atoms_in_conslist cl = 
  (List.fold_right (fun c -> fun l -> LexpSet.union (atoms_in_cons c) l) cl LexpSet.empty)

let rec vars_in_lexp lexp = 
  match lexp with
    | LVar (v,t) -> LexpSet.add (LVar (v,t)) LexpSet.empty
    | Label n -> LexpSet.empty
    | Join (le,le') -> LexpSet.union (vars_in_lexp le) (vars_in_lexp le')

let vars_in_cons c =
  match c with
    | Leq (le,le') -> LexpSet.union (vars_in_lexp le) (vars_in_lexp le')

let vars_in_conslist cl = 
  (List.fold_right (fun c -> fun l -> LexpSet.union (vars_in_cons c) l) cl LexpSet.empty)

let join l1 l2 = 
  match (l1,l2) with
    | (Label n, Label m) -> if n > m then (Label n) else (Label m)
    | (_,_) -> raise (Failure "cannot join non-labels")

let leq l1 l2 =
  match (l1,l2) with
    | (Label a1,Label a2) -> a1 <= a2
    | (_,_) -> raise (Failure "cannot compare non-labels")

let rec eval_lexp rho lexp = 
  match lexp with 
    | LVar (v,t) -> Hashtbl.find rho (LVar (v,t))
    | Label n -> Label n
    | Join (a,le) -> 
	let n = eval_lexp rho a
	and m = eval_lexp rho le 
	in
	  join n m

let cl = []

let rm_solve cl = 
  let vars = vars_in_conslist cl in
  let rho = Hashtbl.create (LexpSet.cardinal vars) in
  let is_rhs_variable (Leq (le,a)) = 
    match a with 
      | LVar (v,t) -> true 
      | Label n -> false 
      | _ -> raise (Failure ("constraint does not have atomic rhs"))
  in
    LexpSet.iter (fun v -> Hashtbl.add rho v bottom) vars;
    let wl = List.filter is_rhs_variable cl in
      (*Printf.printf("worklist: %s\n") (String.concat ";" (List.map cons_to_string wl));*)
    let check_list = List.filter (fun c -> not (is_rhs_variable c)) cl in
    let check_constraint c = 
      match c with 
	  Leq (le,a) ->
	    let leLabel = eval_lexp rho le
	    and vLabel = eval_lexp rho a
	    in
	      leq leLabel vLabel in
    let adjust_bound c wl = 
      (*(Printf.printf("%s: checking\n") (cons_to_string c));*)
      match c with 
	| Leq (le,LVar (v,t)) ->
	    (* check if the lhs is <= rhs *)
	    if (check_constraint c) then 
	      []
	    else
	      (* update rho to be the join of vLabel and leLabel *)
	      let leLabel = eval_lexp rho le
	      and vLabel = eval_lexp rho (LVar (v,t)) in
	      let theJoin = (join vLabel leLabel) in
		(match theJoin with
		   | (Label j) ->
		       begin
			 Hashtbl.replace rho (LVar (v,t)) (Label j);
			 let filter con =
			   (if con = c then
			      false
			    else
			      match con with
				| Leq (le,a) -> LexpSet.mem (LVar (v,t)) (vars_in_lexp le)) in
			   (* find all the constraints in wl that mention v on the lhs -- 
			      but don't include c... *)
			   List.filter filter wl
		       end 
		   | _ -> raise (Failure "result of join is not a label?"))
	| Leq (le,_) -> raise (Failure "non-definite constraint")
    in
    let rec iterate_wl wl = 
      match wl with
	| [] -> ()
	| _ -> iterate_wl (List.concat (List.map (fun c -> adjust_bound c wl) wl)) in
      iterate_wl wl;
      List.iter (fun c -> 
		   if not (check_constraint c) then 
		     raise (Failure ((cons_to_string c) ^ " failed"))) check_list
