(* formal concept analysis implementation *)

open Graph
open Set

module type PrintableOrderedType = 
sig
  include OrderedType
  val to_string : t -> string
end

module FormalConceptAnalysis =
  functor (Obj : PrintableOrderedType) -> 
    functor (Attr : PrintableOrderedType) ->
struct

  let fca_debug = false

  module ObjSet = Set.Make(Obj)
  module AttrSet = Set.Make(Attr)

  module LatticeElement = 
    struct
      type t = ObjSet.t * AttrSet.t
      let compare = compare
      let hash = Hashtbl.hash
      let equal = (=)
    end

  module LatticeElementSet = Set.Make(LatticeElement)

  module LatticeGraph = Imperative.Digraph.Concrete(struct type t = int let compare = compare let equal = (=) let hash = Hashtbl.hash end)
  
  let emptyPair = (ObjSet.empty,AttrSet.empty)
  let obj e = fst e
  let attr e = snd e

  let supremum = ref emptyPair
  let sup_id = ref (-1)

  let idToElement = Hashtbl.create 10
  let elemToId = Hashtbl.create 10

  let current_id = ref (-1)
  let get_new_id v = 
    (current_id := (!current_id) + 1);
    Hashtbl.replace idToElement (!current_id) v;
    Hashtbl.replace elemToId v (!current_id);
    (!current_id)

  let clear_fca () = 
    current_id := (-1);
    Hashtbl.clear idToElement;
    Hashtbl.clear elemToId

(*
  let elem id = Printf.printf ("about to find elem for %d\n") id; let e = Hashtbl.find idToElement id in Printf.printf ("success\n"); e
  let id e = Printf.printf ("about to find id\n"); let i = Hashtbl.find elemToId e in Printf.printf ("success\n"); i
*)
  let elem id = Hashtbl.find idToElement id
  let id e = Hashtbl.find elemToId e

  exception Termination

  let new_lattice () = clear_fca (); LatticeGraph.create ()

  let attrset_to_str at = "{" ^ (String.concat ";" (List.map Attr.to_string (AttrSet.elements at))) ^ "}"
  let objset_to_str os = "{" ^ (String.concat ";" (List.map Obj.to_string (ObjSet.elements os))) ^ "}"
  let elem_to_str (os,at) = "(" ^ (objset_to_str os) ^ "," ^ (attrset_to_str at) ^ ")"

  let add_new_association l x fx =
    try 
      if (fca_debug) then
	Printf.printf ("// NEW ASSOCIATION: %s to %s\n") (Obj.to_string x) (attrset_to_str fx);
      if (!sup_id == -1) then
	begin
	  let new_id = get_new_id (ObjSet.singleton x, fx) in
	    supremum := (ObjSet.singleton x, fx);
	    sup_id := new_id;
	    LatticeGraph.add_vertex l (!sup_id)
	end
      else
	begin
	  if not (AttrSet.subset fx (attr (!supremum))) then
	    begin
	      if (obj (!supremum)) = ObjSet.empty then
		begin
		  Hashtbl.remove elemToId (!supremum);
		  supremum := (ObjSet.empty,AttrSet.union (attr (!supremum)) fx);
		  Hashtbl.replace idToElement (!sup_id) (!supremum);
		  Hashtbl.replace elemToId (!supremum) (!sup_id);
		  if (fca_debug) then
		    Printf.printf ("// updating the supremum to be %s\n") (elem_to_str !supremum)
		end
	      else
		begin
		  let new_top = (ObjSet.empty,AttrSet.union (attr (!supremum)) fx) in
		  let new_id = get_new_id new_top in
		    if (fca_debug) then
		      Printf.printf "// adding %s to graph with id %d and linking to %s\n" (elem_to_str new_top) (new_id) (elem_to_str !supremum); 
		    LatticeGraph.add_vertex l new_id;
		    LatticeGraph.add_edge l (!sup_id) new_id;
		    supremum := new_top;
		    sup_id := new_id
		end;
	    end
	end;
      let c_buckets = Hashtbl.create 10 and
	  c'_buckets = Hashtbl.create 10 and
	  max_card = ref 0 in
	LatticeGraph.iter_vertex 
	  (fun v_id ->
	     let v = elem v_id in
	     let i = AttrSet.cardinal (attr v) in
	       if (i > !max_card) then
		 max_card := i;
	       if (Hashtbl.mem c_buckets i) then
		 Hashtbl.replace c_buckets i 
		   (LatticeElementSet.add v (Hashtbl.find c_buckets i))
	       else
		 Hashtbl.replace c_buckets i 
		   (LatticeElementSet.singleton v);
	       Hashtbl.replace c'_buckets i (LatticeElementSet.empty))
	  l;
	for i = 0 to (!max_card) do 
	  if (Hashtbl.mem c_buckets i) then
	    LatticeElementSet.iter 
	      (fun v ->
		 let v_id = id v in
		   if AttrSet.subset (attr v) fx then
		     begin
		       if (fca_debug) then
			   Printf.printf ("// subset time -- %s is a subset of %s for node %s, so adding new elements\n") (attrset_to_str (attr v)) (attrset_to_str fx) (elem_to_str v);
		       Hashtbl.remove elemToId v;
		       let new_v = (ObjSet.add x (obj v),attr v) in
			 Hashtbl.replace idToElement v_id new_v;
			 Hashtbl.replace elemToId new_v v_id;
			 Hashtbl.replace c'_buckets i (LatticeElementSet.add new_v (Hashtbl.find c'_buckets i));
		     end;
		   let v = elem v_id in 
		     if (fca_debug) then 
		       Printf.printf ("// comparing %s and %s -- are they equal?\n") (attrset_to_str (attr v)) (attrset_to_str fx);
		     if (attrset_to_str (attr v) = (attrset_to_str fx)) then 
		       begin
			 if (fca_debug) then
			   Printf.printf ("// yes they are, we are done\n");
			 raise Termination
		       end
		     else
		       let inter = AttrSet.inter (attr v) fx in
			 if (fca_debug) then
			   Printf.printf ("// guess not!\n");
			 let inter_size = AttrSet.cardinal inter in
			 let c'_inter = 
			   if (Hashtbl.mem c'_buckets inter_size) then 
			     Hashtbl.find c'_buckets inter_size 
			   else 
			     LatticeElementSet.empty in
			 let is_generator = 
			   LatticeElementSet.fold 
			     (fun h1 gen ->
				if not gen then 
				  false
				else 
				  if (attr h1 = inter) then
				    false
				  else
				    true) 
			     (c'_inter)
			     true
			 in
			   if (is_generator) then
			     begin
			       if (fca_debug) then
				 Printf.printf "// element %s is a generator\n" (elem_to_str v);
			       let hn = (ObjSet.add x (obj v),inter) in
			       let hn_id = get_new_id hn in
				 if (fca_debug) then
				   Printf.printf "// adding %s to graph with id %d\n" (elem_to_str hn) (hn_id);
				 LatticeGraph.add_vertex l hn_id;
				 LatticeGraph.add_edge l hn_id v_id;
				 Hashtbl.replace c'_buckets inter_size (LatticeElementSet.add hn c'_inter);
				 for j = 0 to (inter_size - 1) do
				   if (Hashtbl.mem c'_buckets j) then
				     LatticeElementSet.iter 
				       (fun ha -> 
					  if (fca_debug) then
					    Printf.printf ("// going to check subset -- %b\n") (Hashtbl.mem elemToId ha);
					  if AttrSet.subset (attr ha) inter then
					    let parent = ref true in
					    let ha_id = id ha in
					      if (fca_debug) then
						Printf.printf ("// iter time\n");
					      LatticeGraph.iter_pred
						(fun hd_id -> 
						   if AttrSet.subset (attr (elem hd_id)) inter then 
						     parent := false)
						l ha_id;
					      if (fca_debug) then
						Printf.printf ("// done deciding about parent\n");
					      if (!parent) then
						begin
						  if (LatticeGraph.mem_edge l v_id ha_id) then
						    begin
						      LatticeGraph.remove_edge l v_id ha_id;
						      LatticeGraph.remove_edge l ha_id v_id;
						      if (fca_debug) then
							Printf.printf ("// removing edge\n");
						    end;
						  if (fca_debug) then
						    Printf.printf ("// adding edge\n");
						  LatticeGraph.add_edge l ha_id hn_id
						end)
				       (Hashtbl.find c'_buckets j)
				 done;
				 if (fca_debug) then
				   Printf.printf ("// comparing %s and %s -- are they equal?\n") (attrset_to_str inter) (attrset_to_str fx);
				 if (attrset_to_str inter) = (attrset_to_str fx) then 
				   begin
				     if (fca_debug) then 
				       Printf.printf ("// yes they are, we are done\n");
				     raise Termination
				   end;
				 if (fca_debug) then 
				   Printf.printf ("// no they are not\n");
			     end)
	      (Hashtbl.find c_buckets i)
	done
    with Termination -> ()

  let print_lattice l =
    LatticeGraph.iter_vertex 
      (fun v_id -> let v = elem v_id in 
	 Printf.printf ("#%d: (%s,%s)\n") v_id 
	   (objset_to_str (obj v)) (attrset_to_str (attr v));
	 Printf.printf ("\tedges to: %s\n") (String.concat (", ") (List.map string_of_int (LatticeGraph.succ l v_id)))
      )
      l;
    Printf.printf ("size %d\n") (LatticeGraph.nb_vertex l)

  let lattice_to_dot file l n = 
    Printf.fprintf file ("digraph L%d {\n") n;
    LatticeGraph.iter_vertex 
      (fun v_id -> let v = elem v_id in 
	 Printf.fprintf file ("\tn%d [label=\"(%s,%s)\"];\n") v_id (objset_to_str (obj v)) (attrset_to_str (attr v)))
      l
    ;
    LatticeGraph.iter_edges 
      (fun v1 v2 -> 
	 Printf.fprintf file ("\tn%d -> n%d;\n") v1 v2
      )
      l;
(*
    LatticeGraph.iter_vertex 
      (fun v1 -> 
	 LatticeGraph.iter_vertex 
	   (fun v2 ->
	      if (v1 != v2 && ObjSet.subset (obj (elem v1)) (obj (elem v2))) then
		Printf.printf ("\tn%d -> n%d;\n") v1 v2
	   )
	   l
      )
      l;
*)
    Printf.fprintf file ("}\n")
end
(*
module IntFCA =
  struct
    type t = int
    let compare = compare
    let to_string = string_of_int
  end

module StringFCA = 
  struct 
    type t = string
    let compare = compare
    let to_string = (fun x -> x)
  end

module TestFCA = FormalConceptAnalysis(IntFCA)(StringFCA)

let _ = 
  let lat = TestFCA.new_lattice ()
  in
    List.iter
      (fun (obj,attr) -> TestFCA.add_new_association lat obj attr)
(*      [("composite",List.fold_right TestFCA.AttrSet.add [4;6;8;9] TestFCA.AttrSet.empty);
       ("odd", List.fold_right TestFCA.AttrSet.add [1;3;5;7;9] TestFCA.AttrSet.empty)];*)
      [
	(1,List.fold_right TestFCA.AttrSet.add ["odd";"square"] TestFCA.AttrSet.empty);
	(2,List.fold_right TestFCA.AttrSet.add ["even";"prime"] TestFCA.AttrSet.empty);
	(3,List.fold_right TestFCA.AttrSet.add ["odd";"prime"] TestFCA.AttrSet.empty);
	(4,List.fold_right TestFCA.AttrSet.add ["even";"composite";"square"] TestFCA.AttrSet.empty);
(*	(5,List.fold_right TestFCA.AttrSet.add ["odd";"prime"] TestFCA.AttrSet.empty);*)
	(6,List.fold_right TestFCA.AttrSet.add ["composite";"even"] TestFCA.AttrSet.empty);
(*	(7,List.fold_right TestFCA.AttrSet.add ["odd";"prime"] TestFCA.AttrSet.empty);*)
	(8,List.fold_right TestFCA.AttrSet.add ["composite";"even"] TestFCA.AttrSet.empty);
(*	(9,List.fold_right TestFCA.AttrSet.add ["composite";"odd";"square"] TestFCA.AttrSet.empty);
	(10,List.fold_right TestFCA.AttrSet.add ["composite";"even"] TestFCA.AttrSet.empty);*)
      ];
    TestFCA.lattice_to_dot stdout lat 0

*)
