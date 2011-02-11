module type OfStringSet = 
  sig
    include Set.S

    val string_of_set : t -> string
  end

module FeasibleSets = functor (S : OfStringSet) ->
  struct

    (* 
     * k -> continuation to pass sets to 
     * depList -> dependency list (in pairs)
     * universeList -> all sets in the universe
     *)
    let enumerate_feasible_sets k depList universeList = 
      let dep x = 
	List.fold_left 
	  (fun depset -> fun (y,l) -> 
	     if y = x then S.add l depset else depset)
	  S.empty 
	  depList in
      let r j = 
	(* all elements of j without dependencies in j -- 
	   we can remove j without making the set unfeasible 
	*)
	S.fold 
	  (fun elt -> fun depset -> 
	     let elt_dep = dep elt in
	       (*Printf.printf "dependencies of %d: %s\n" elt (S.string_of_intset elt_dep);*)
	       if S.is_empty (S.inter elt_dep j) || (S.is_empty elt_dep) then
		 S.add elt depset 
	       else
		 depset)
	  j
	  S.empty
      in 
      let universe = 
	List.fold_right S.add universeList S.empty
      in
      let rec enumerate_helper j = 
	(* find first element in universe that is not in j *)
	let next = 
	  S.fold 
	    (fun elt -> fun a -> 
	       match a with
		   None -> 
		     if not (S.mem elt j) then
		       Some elt
		     else 
		       a
		 | Some _ -> a)
	    universe
	    None in
	  (* include this element in j *)
	  match next with
	    | None -> ()
	    | Some first_not_in_j -> 
		let newj = S.add first_not_in_j j in
		  (* for the previous elements of the universe -- check to see
		     if they have no dependencies in j.  if so, remove them. *)
		let checkj = S.elements (S.filter (fun elt -> elt < first_not_in_j) newj) in
		let nextj = List.fold_right
		  (fun elt -> fun j -> 
		     (* if elt is in R(J), remove it from j *)
		     let rj = (r j) in
		       (*Printf.printf "r(%s) : %s -- looking at %d\n" (S.string_of_intset j) (S.string_of_intset rj) elt;*)
		       if (S.mem elt rj) then
			 S.remove elt j
		       else 
			 j) 
		  checkj
		  newj
		in
		  (* output j and recurse *)
		  (k nextj);
		  enumerate_helper nextj
      in
	enumerate_helper S.empty
  end
