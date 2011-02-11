open Graph

let do_min_cut = false

module type INT_GRAPH =
sig
  include Graph.Sig.I with type V.t = int and type E.label = int

  val nodeForTag : V.t -> Simp.lexp
  val tagForNode : Simp.lexp -> V.t
  val infinity_hack : int
  val id_for_node : V.t -> string option

  val graph_attributes : t -> Graph.Graphviz.DotAttributes.graph list 
  val default_vertex_attributes : 
      t -> Graph.Graphviz.DotAttributes.vertex list 
  val vertex_name : V.t -> string 
  val vertex_attributes : V.t -> Graph.Graphviz.DotAttributes.vertex list 
  val get_subgraph : V.t -> Graph.Graphviz.DotAttributes.subgraph option 
  val default_edge_attributes : t -> Graph.Graphviz.DotAttributes.edge list 
  val edge_attributes : E.t -> Graph.Graphviz.DotAttributes.edge list 

  val v_to_string : V.t -> string
  val procedure_for_node : V.t -> int option
  val e_to_string : E.t -> string
  val edgelabel_to_string : E.label -> string
end

module Compactor = functor (G : INT_GRAPH) ->
struct
  open Simp


  module DOT = Graphviz.Dot(G)

  module IntSet = Set.Make(struct type t = int let compare = compare end) 
  let edgeToProcedureMap : ((int * int),IntSet.t) Hashtbl.t = Hashtbl.create 10
  let idToProcedureMap : (int,string) Hashtbl.t = Hashtbl.create 10

  module EdgeLabel = 
    struct
      type t = int
      type label = t

      let max_capacity l = l
      let min_capacity l = 0
      let flow _ = 0
      let add = (+)
      let sub = (-)
      let zero = 0
      let compare = compare
    end

  module VSet = Set.Make(G.V)
  module FF = Flow.Ford_Fulkerson(G)(EdgeLabel)
  module PathChecker = Path.Check(G)

  let convert_list_to_table procedureList =
    List.iter (fun (p,i) -> Hashtbl.replace idToProcedureMap i p) procedureList

  let get_sub_lv_node s lexp =
    match lexp with 
      | (LVar (lv,t)) -> LVar (lv,s :: t) 
      | _ -> raise (Failure "cannot get sub lv node for non-lvar")

  let get_incoming_lv_node = get_sub_lv_node `Incoming
  let get_outgoing_lv_node = get_sub_lv_node `Outgoing
  let get_incoming_node a = 
		match a with 
		  | LVar (ExpLVar l,t) -> get_incoming_lv_node a
		  | _ -> a 
  let get_outgoing_node a = 
		match a with 
		  | LVar (ExpLVar l,t) -> get_outgoing_lv_node a
		  | _ -> a

  let compact g procedureList = 
    (* new graph will map everything in g that is a member of procedureList into one node *)
    let compacted_graph = G.create () in
    let proc_for_node v = match G.procedure_for_node v with Some s -> s | None -> -1 in
      (*G.iter_vertex (fun v -> Printf.printf ("%s : procedure #%d\n") (G.v_to_string v) (proc_for_node v)) g;*)
        (* hash tables that we will use *)
      let nodeToProcId = Hashtbl.create 10 in
      let procIdToOutgoing = Hashtbl.create 10 in
      let procIdToIncoming = Hashtbl.create 10 in
      convert_list_to_table procedureList;
      let nameTable = idToProcedureMap in 
      (* helper functions that we will use *)
      let is_mapped v = try (Hashtbl.find nodeToProcId v != -1) with Not_found -> false in
      let add_mapping t add_fn k v = Hashtbl.replace t k (add_fn v (Hashtbl.find t k)) in
      let add_outgoing_mapping = add_mapping procIdToOutgoing VSet.add in
      let add_incoming_mapping = add_mapping procIdToIncoming VSet.add in
      let name_for_procid id = if (Hashtbl.mem nameTable id) then (Hashtbl.find nameTable id) else "[NONE]" in
	Printf.printf ("about to compact!\n");
	flush stdout;
	G.iter_vertex (fun v -> 
			 Hashtbl.replace nodeToProcId v (proc_for_node v);
			 Hashtbl.replace procIdToOutgoing (proc_for_node v) (VSet.empty);
			 Hashtbl.replace procIdToIncoming (proc_for_node v) (VSet.empty)
		      ) g;
	G.iter_edges (fun v1 -> fun v2 -> 
			if ((is_mapped v1) && not (is_mapped v2)) then
			  add_outgoing_mapping (proc_for_node v1) v2
			else if ((not (is_mapped v1)) && (is_mapped v2)) then
			  add_incoming_mapping (proc_for_node v2) v1
			else 
			  ()
		     ) g;
	(* STILL DON'T UNDERSTAND: ROLE OF LATTICE LABELS INSIDE 
	   PROCEDURES -- MAKE SURE THIS WORKS *)
	Printf.printf ("about to start connecting edges! size %d\n") (G.nb_vertex compacted_graph);
	flush stdout;
	G.iter_vertex (fun v ->
			 if (not (is_mapped v)) then
			   G.add_vertex compacted_graph v)
	  g;
	Printf.printf ("graph size: original: %d vs compacted: %d\n") (G.nb_vertex g) (G.nb_vertex compacted_graph); 
	G.iter_edges_e (fun e ->
			  let src = G.E.src e and
			      dst = G.E.dst e in
			    if (not (is_mapped src) && not (is_mapped dst)) then
			      G.add_edge_e compacted_graph e)
	  g;
	(* for each procedure list, iterate over its incoming/outgoing nodes and try to hook them up *)
	if (!Simputil.debug) then
	  Hashtbl.iter (fun id -> fun set -> 
			  Printf.printf ("%s (outgoing %d): %s\n") (name_for_procid id) id (String.concat ";" (List.map G.v_to_string (VSet.elements set)))) 
	    procIdToOutgoing;
	Printf.printf ("time to hook edges together!\n");
	flush stdout;
	let graph_path = PathChecker.create g in
	  Hashtbl.iter (fun k -> fun _ -> 
			  (*Printf.printf ("compacted graph size now: %d\n") (G.nb_vertex compacted_graph);*)
			  (*if (!Simputil.debug) then*)
			  if (Hashtbl.mem procIdToIncoming k) then 
			    let incoming = Hashtbl.find procIdToIncoming k in
			    let outgoing = Hashtbl.find procIdToOutgoing k in
			      if (!Simputil.debug) then
				begin
				  Printf.printf ("iterating over proc Id map -- %d (%d) outgoing: %d incoming: %d\n") k (Hashtbl.length nameTable) (VSet.cardinal outgoing) (VSet.cardinal incoming);
				  Printf.printf ("outgoing: %s\n") (String.concat ";\n\t" (List.map G.v_to_string (VSet.elements outgoing)));
				  Printf.printf ("incoming: %s\n") (String.concat ";\n\t" (List.map G.v_to_string (VSet.elements incoming)));
				end;
			      flush stdout;
			      let name = name_for_procid k in
				VSet.iter 
				  (fun inc -> 
				     VSet.iter 
				       (fun out ->
					  flush stdout;
					  let (max_flow) = 
					    (*FF.maxflow g inc out *)
					    if (PathChecker.check_path graph_path inc out) then
					      1 
					    else
					      0
					  in
					    if (!Simputil.debug) then
					      Printf.printf 
						("maximum flow between %s and %s is %d\n")
						(G.v_to_string inc) (G.v_to_string out) max_flow;
					    if (max_flow != 0 && max_flow != G.infinity_hack) then
					      begin
						G.add_edge_e compacted_graph (G.E.create inc (max_flow) out);
						let current_mapping = 
						  if (Hashtbl.mem edgeToProcedureMap (inc,out)) then
						    Hashtbl.find edgeToProcedureMap (inc,out)
						  else
						    IntSet.empty in
						let new_mapping = (IntSet.add k current_mapping) in
						  Hashtbl.replace edgeToProcedureMap (inc,out) new_mapping
					      end
				       )
				       outgoing
				  ) incoming
		       )
	    nameTable;
	  DOT.output_graph (open_out ("compact.dot")) compacted_graph;
	  Printf.printf ("final size!  %d\n") (G.nb_vertex compacted_graph);
	  compacted_graph
end
