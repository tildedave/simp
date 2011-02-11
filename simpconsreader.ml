(* read constraints from an XML file *)

open Simp
open Xml

module StringSet = Set.Make(struct type t = string let compare = compare end)

module type XMLCONSTRAINTREADER = 
  sig
    val nvToExpMap : (string, string) Hashtbl.t
    val nvToPosMap : (string, string) Hashtbl.t
    val nvToWeightMap : (string, int) Hashtbl.t
    val nvNoDeclassify : StringSet.t ref
    val xml_file_to_constraint_set : string -> (Simp.cons list * Simp.LatticeGraph.t * ((string * int) list))
  end

module XmlConstraintReaderImpl =
struct


  type lattice_info = LatticeElement of string * int | LatticeLeq of int * int | LatticeBottom of int
  type lattice = Lattice of (lattice_info list) * (lattice_info list)

  type constraint_element = 
    | Constraint of cons 
    | LatticeConstraintElement of lattice
    | ProcedureList of (string * int) list

  module AttrMap = Map.Make(struct type t = string let compare = compare end)

  let nvToExpMap = Hashtbl.create 100
  let nvToPosMap = Hashtbl.create 100
  let nvToWeightMap = Hashtbl.create 100
  let nvNoDeclassify = ref (StringSet.empty)

  let file_to_string filename = 
    let filein = open_in filename in
    let rec file_to_string_helper l = 
      try
	let next = input_line filein in
	  file_to_string_helper (next :: l)
      with End_of_file -> l
    in
      String.concat "\n" (file_to_string_helper [])

  let get_element_with_name n = 
    try
      List.find (fun xml ->
		   match xml with 
		     | (Element (en,l,xml)) -> n = en
		     | _ -> raise (Failure "list contains non-element"))
    with
	Not_found -> raise (Failure ("couldn't find element with name " ^ n))
	
  let element_to_label constraint_attrs xml =
    try 
    match xml with 
      | Element (ns,attrlist,xml_labels) ->
	  if (List.mem_assoc "name" attrlist) then
	    let name = List.assoc "name" attrlist in
	      (match (List.assoc "isvar" attrlist) with
		 | "true" -> 
		     let (var,uniqKey,expStr) = 
		       if (Str.string_match (Str.regexp "^pc\\([0-9]+\\)") name 0) then
			 let pcNumStr = (Str.matched_group 1 name) in
			   if (!Simputil.pc_decl == true) then 
			     (ExpLVar ("pc" ^ pcNumStr),("pc" ^ pcNumStr),Some (Hashtbl.find nvToPosMap ("pc" ^ pcNumStr)))
			   else
			     (PCLVar (int_of_string pcNumStr),"pc" ^ pcNumStr,None)
		       else if (Str.string_match (Str.regexp "^\\(NV[0-9]+\\|PARAM[0-9]+\\)") name 0) then
			 begin
			   let nv = (Str.matched_group 1 name) in
			   (ExpLVar name,name,
			    try
			      Some (Hashtbl.find nvToExpMap nv)
			    with Not_found ->
			      None)
			 end
		       else 
			 (VarLVar name,name,None)
		     in
		       begin
			 let weight = 
			   if (List.mem_assoc "weight" attrlist) then
			     int_of_string (List.assoc "weight" attrlist) 
			   else 
			     1 in
			   Hashtbl.replace nvToWeightMap name weight;
			   let canDecl = 
			     if (List.mem_assoc "canDecl" attrlist) then 
			       (*bool_of_string (List.assoc "canDecl" attrlist)*)
			       true
			     else
			       true in
			   let expStrEntry = 
			     match expStr with 
			       | None -> []
			       | Some s -> [`ExpStr s] in
			     if not (canDecl) then
			       nvNoDeclassify := StringSet.add uniqKey (!nvNoDeclassify);
			     let procedureId = 
			       if (List.mem_assoc "procedure" attrlist) then
				 if (List.assoc "procedure" attrlist) = "" then
				   -1 
				 else
				   int_of_string (List.assoc "procedure" attrlist)
			       else
				 -1 in
			       LVar (var,[`UniqId uniqKey; `Weight weight; `Procedure procedureId ] @ expStrEntry)
		       end
		 | "false" -> 
		     let regexp = Str.regexp "LATTICE#\\([0-9]+\\)" in
		       if (Str.string_match regexp name 0) then
			 let labelNum = int_of_string (Str.matched_group 1 name) in
			   (Label labelNum)
		       else
			 raise (Failure ("couldn't find a label number for non-variable with name " ^ name))
		 | _ -> raise (Failure "isvar not true or false"))
	  else
	    (* there is no name -- this only happens when the 
	       element being converted to a label corresponds to the 
	       Jif "0" label.  here we return bottom  -- 
	       NOTE: I had to manually code bottom to be 0.
	    *)
	    (Label 0)
      | PCData n -> raise (Failure "cannot convert non-element to label")
    with
	Not_found -> raise (Failure "couldn't convert element to label")

  let element_to_lexp constraint_attrs xml = 
    match xml with
      | Element (el,l,xml_labels) ->
	  let labels = List.map (element_to_label constraint_attrs) xml_labels in
	  let make_join l1 l2 = Join (l1,l2) in
	    (match (List.length labels) with 
	       | 0 -> Printf.printf ("el: %s") el; (Label 0) (*raise (Failure "join of no labels -- TODO: make this into BOTTOM")*)
	       | 1 -> List.hd labels 
	       | _ -> List.fold_left make_join (List.hd labels) (List.tl labels))
      | PCData n -> raise (Failure "cannot convert non-element to label")

  let unfilter_string s = 
    Str.global_replace (Str.regexp "#gt") ">" 
      (Str.global_replace (Str.regexp "#lt") "<"
	 (Str.global_replace (Str.regexp "#amp") "&" s))

  let get_xml_value xml =
    match xml with
      | PCData n -> n
      | Element (n,l,xml_labels) -> 
	  match xml_labels with
	      [PCData n] -> unfilter_string n
	    | _ -> ""
(*
		Printf.printf ("xml_labels: %d\n") (List.length xml_labels);
		raise (Failure ("get_xml_value doesn't have pc data, and I'm dumb -- " ^ n))*)

  let element_to_constraint xml =
    match xml with
      | Element ("con",l,xml) ->
	  let con_elem = get_element_with_name "asString" xml and
	      bc_elem = get_element_with_name "because" xml and
	      pos_elem = get_element_with_name "pos" xml
	  in
	  let con = get_xml_value con_elem and
	      bc = get_xml_value bc_elem and
	      pos = get_xml_value pos_elem
	  in
	    (
	      let regexp = Str.regexp ".*\\(NV[0-9]+\\|PARAM[0-9]+\\|pc[0-9]+\\).*==.*" in
	      let add_defn () = 
		let nv = Str.matched_group 1 con in
		  begin
		    Hashtbl.replace nvToExpMap nv bc;
		    Hashtbl.replace nvToPosMap nv pos
		  end in
		if (Str.string_match regexp con 0) then
		  add_defn ()
		else if (Str.string_match (Str.regexp ".*== {\\(PARAM[0-9]+\\)}.*") con 0) then
		  add_defn ()
	    );
	    let lhs_elem = get_element_with_name "lhs" xml and
		rhs_elem = get_element_with_name "rhs" xml in
	    let attrmap = AttrMap.add "because" bc AttrMap.empty in
	    let lhs = element_to_lexp attrmap lhs_elem and
		rhs = element_to_label attrmap rhs_elem 
	    in
	      Leq (lhs,rhs)
      | _ -> raise (Failure "tried to convert non-con element into constraint")
	  

  let element_to_lattice_info e =
    match e with 
      | Element ("label",tagList,xml) ->
	  let name = List.assoc "name" tagList in
	  let id = List.assoc "id" tagList in
	    LatticeElement (name,int_of_string id)
      | Element ("lt",tagList,xml) ->
	  let lhs = List.assoc "lhs" tagList and
	      rhs = List.assoc "rhs" tagList in
	    LatticeLeq (int_of_string lhs,int_of_string rhs)
      | _ -> raise (Failure "tried to convert non-lattice information element into lattice information")

  let element_to_lattice e = 
    match e with
      | Element ("lattice",l,xml) -> 
	  let lattice_info = List.map element_to_lattice_info xml in
	  let lattice_elems = List.filter (fun x -> match x with LatticeElement _ -> true | _ -> false) lattice_info and
	      lattice_leq = List.filter (fun x -> match x with LatticeLeq _ -> true | _ -> false) lattice_info 
	  in
	    Lattice (lattice_elems,lattice_leq)
      | _ -> raise (Failure "tried to convert non-lattice element into lattice")

  let element_to_procedure e =
    match e with
      | Element ("procedure",tagList,xml) ->
	  let name = List.assoc "name" tagList and
	      id = List.assoc "id" tagList in
	    (name,int_of_string id)

  let element_to_procedurelist e =
    match e with
      | Element ("procedureList",l,xml) ->
	  List.map element_to_procedure xml

  let element_to_constraint_element e = 
    match e with 
      | Element ("con",_,_) -> Some (Constraint (element_to_constraint e))
      | Element ("lattice",_,_) -> Some (LatticeConstraintElement (element_to_lattice e))
      | Element ("procedureList",_,_) -> Some (ProcedureList (element_to_procedurelist e))
      | _ -> raise (Failure "tried to convert invalid element into constraint element")

  let constraint_set_to_list l xml = 
    (* each element in xml should be a constraint, a description of a lattice, or a procedure mapping *)
    let cons_elements = 
      (* remove the None elements, strip off the Some from those remaining *)
      List.map (fun (Some s) -> s) (List.filter (fun maybe -> match maybe with Some s -> true | None -> false)  
				      (List.map element_to_constraint_element xml)) in
    let lattice = List.fold_left (fun lattice -> fun x -> match x with LatticeConstraintElement l -> Some l | _ -> lattice) None cons_elements and
	constraints = List.fold_left (fun l -> fun x -> match x with Constraint c -> c :: l | _ -> l) [] cons_elements and
	procedureList = List.fold_left (fun p -> fun x -> match x with ProcedureList pl -> pl | _ -> p) [] cons_elements in
      (match lattice with 
	   Some (Lattice (elems,deps)) ->
	     let graphWithVertices = 
	       List.fold_left 
		 (fun graph le ->
		    match le with 
		      | LatticeElement (s,id) -> 
			  LatticeGraph.add_vertex graph (s,id)
		      | _ -> raise (Failure "cannot happen -- lattice graph only contains lattice elements"))
		 LatticeGraph.empty 
		 elems in
	     let graphWithEdges = 
	       List.fold_left
		 (fun graph leq -> 
		    match leq with
			LatticeLeq (id1,id2) ->
			  let maybe_v1 = LatticeGraph.vertex_for_id id1 graph and
			      maybe_v2 = LatticeGraph.vertex_for_id id2 graph in
			    (match maybe_v1,maybe_v2 with
				 Some v1, Some v2 ->
				   LatticeGraph.add_edge graph v1 v2
			       | _ -> raise (Failure ("couldn't find vertices for ids" ^ (string_of_int id1) ^ " and " ^ (string_of_int id2))))
		      | _ -> raise (Failure "cannot happen -- lattice dependencies only contains lattice leq"))
		 graphWithVertices
		 deps in 
	       (constraints,graphWithEdges,procedureList)
	 | None ->
	     (* no lattice -- use default two point lattice *) 
	     (constraints,defaultLattice,procedureList))
	(*Printf.printf "%s\n" (String.concat ";\n" (List.map cons_to_string cons))*)
	(*cons*)

  let xml_file_to_constraint_set fn = 
    try
      let x = Xml.parse_file fn in
	match x with
	  | Element ("constraint-set",l,xml) -> 
	      constraint_set_to_list l xml
	  | _ -> raise (Failure "tried to convert non-constraint-set into constraint set")
    with
	Xml.Error err -> 
	  Printf.printf "got XML parsing error: %s\n" (error err);
	  raise (Failure "XML parsing error")

end

module XmlConstraintReader = (XmlConstraintReaderImpl : XMLCONSTRAINTREADER)
