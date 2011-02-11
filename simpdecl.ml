open Simp
open Simputil
open Dominators
open Simpgraph.SimpGraph
open Simpconsreader
open Pivotlister
open Fca
open Graph

module FlowGraphDominators = Dominfast.Dominators(FlowGraph)
module Enumerater = EnumerateCuts(FlowGraph)(FlowGraph.EdgeLabel)
module Compactor = Compactor.Compactor(FlowGraph)
module DOT = Graphviz.Dot(FlowGraph)

let constraint_set_to_flowgraph cons name lattice =
  let congraph = timeThunk 
    (fun _ -> 
       if (!Simputil.verbose) then
	 begin
	   Printf.printf ("building graph...\n");
	   flush stdout
	 end;
       (FlowGraph.constraint_set_to_flowgraph cons lattice))
    (SimpTimer.record_time "build graph")
  in
    FlowGraphDotOutput.output_graph (open_out (name ^ ".dot")) congraph;
    (if (!Simputil.output_dot) then
      let _ = 
	timeThunk 
	  (fun _ -> Sys.command (Printf.sprintf "dot -Tpng %s.dot > %s.png" name name))
	  (SimpTimer.record_time "dot output")
      in
	());
    congraph

let command_to_flowgraph c name = 
  let cons = command_to_constraints c in
    constraint_set_to_flowgraph cons name defaultLattice

module CutElem = struct
  type cut_elem = ExpPos of string * string option | CutOptions of cut_elem * (cut_elem list)
  type t = cut_elem
  let compare = compare

  let rec cut_to_string c = 
    match c with
      | ExpPos (s,p) -> s ^ (match p with None -> "" | (Some s2) -> " (" ^ s2 ^ ")")
      | CutOptions (c,co) -> (cut_to_string c) ^ " |-> [" ^ (String.concat ";" (List.map cut_to_string co)) ^ "]"

  let to_string = cut_to_string
end

module CutSet = struct
  include Set.Make(CutElem)

  let cut_to_string = CutElem.cut_to_string

  let prune_cut s = 
    Printf.printf ("prune %s\n") s;
    let r = Str.regexp ("\\(.*\\): .*") in 
      if (Str.string_match r s 0) then
	Str.matched_group 1 s
      else
	""
  let edge_to_cut_elem (v1,i,v2) = 
    let stripped_name n = 

      if (Str.string_match (Str.regexp ("\\(NV[0-9]+\\|PARAM[0-9]+\\).*")) n 0) then
	Some (Str.matched_group 1 n) 
      else
	None in
    let expStr v id = 
      let default_name = 
	match FlowGraph.expstr_for_node (FlowGraph.GraphLabel.nodeForTag v) with
	  | Some expstr -> "a_" ^ id ^ " (" ^ expstr ^ ")"
	  | None -> "a_" ^ id  in
	match (stripped_name id) with
	    Some sn -> 
	      if (Hashtbl.mem XmlConstraintReader.nvToExpMap sn) then
		(id ^ ": " ^ Hashtbl.find XmlConstraintReader.nvToExpMap sn)
	      else
		default_name
	  | None -> default_name in
    let posStr id = 
      match (stripped_name id) with
	  Some sn -> if (Hashtbl.mem XmlConstraintReader.nvToPosMap sn) then
	    Some (Hashtbl.find XmlConstraintReader.nvToPosMap sn)
	  else 
	    None
	| None -> None in
      match (FlowGraph.GraphLabel.nodeForTag v1,
	     FlowGraph.GraphLabel.nodeForTag v2) with
	| LVar (ExpLVar ev1,tl1),
	  LVar (ExpLVar ev2,tl2) ->
	    (match FlowGraph.id_for_node v1,FlowGraph.id_for_node v2 with
	       | Some id1, Some id2 ->
		   if (FlowGraph.is_incoming_node v1) && 
		     (FlowGraph.is_outgoing_node v2) && 
		     (id1 = id2) then
		       begin
			 CutElem.ExpPos (expStr v1 id1,posStr id1)
		       end
		   else
		     raise (Interrupt ("minimum edge cut does not correspond to expression cut -- " ^ (FlowGraph.v_to_string v1) ^ "," ^ (FlowGraph.v_to_string v2) ^ " not incoming/outgoing pair"))
	       | _ -> raise (Interrupt "minimum edge cut does not correspond to expression cut -- nodes don't have ids"))
	| (a1,a2) -> 
	    if (!Simputil.cluster) then
	      let proc = if (Hashtbl.mem Compactor.edgeToProcedureMap (v1,v2)) then
		Some (String.concat ";" (List.map (Hashtbl.find Compactor.idToProcedureMap) (Compactor.IntSet.elements (Hashtbl.find Compactor.edgeToProcedureMap (v1,v2)))))
	      else
		None in
	      CutElem.ExpPos ((atom_to_string a1) ^ " -> " ^ (atom_to_string a2),proc)
	    else
	      raise (Interrupt ("minimum edge cut does not correspond to expression cut -- not both lvars: " ^ (atom_to_string a1) ^ " and " ^ (atom_to_string a2)))
end


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

module FCA = FormalConceptAnalysis(StringFCA)(IntFCA)

module FasterTransitiveClosure = Transitiveclosure.TransitiveClosure(FlowGraph)

let compute_dominators_from_idom g idom = 
  let dom_graph = FlowGraph.create ~size:(FlowGraph.nb_vertex g) () in
    Hashtbl.iter 
      (fun k v -> 
	 let k_mem = FlowGraph.mem_vertex g k and
	     v_mem = FlowGraph.mem_vertex g v in
	   if (k_mem) then
	     FlowGraph.add_vertex dom_graph k;  
	   if (v_mem) then 
	     FlowGraph.add_vertex dom_graph v;
	   if (k_mem && v_mem) then
	     FlowGraph.add_edge dom_graph k v)
      idom
    ;
    let tc_dom_graph = FasterTransitiveClosure.transitive_closure dom_graph in
    let return_map = Hashtbl.create (FlowGraph.nb_vertex g) in
      FlowGraph.iter_vertex 
	(fun v ->
	   if (FlowGraph.mem_vertex tc_dom_graph v) then
	     Hashtbl.replace return_map v (List.fold_right FlowGraphDominators.VSet.add (FlowGraph.succ tc_dom_graph v) FlowGraphDominators.VSet.empty)
	   else
	     Printf.printf ("%d not in the tc_dom_graph\n") v
	)
	dom_graph;
      (fun q -> 
	 (*Printf.printf ("lookup up %d %b\n") q (Hashtbl.mem return_map q); *)
	 Hashtbl.find return_map q)

let wrap_not_found thunk = 
  try 
    Some (thunk ())
  with Not_found ->
    None

module DeclassifierOutput = 
struct
  let print_flow_header decl_file fromLabel toLabel = 
    match decl_file with 
      | None -> ()
      | Some f -> Printf.fprintf f "\t<flow from=\"%s\" to=\"%s\">\n" fromLabel toLabel

  let print_flow_footer decl_file = 
    match decl_file with 
      | None -> ()
      | Some f -> Printf.fprintf f "\t</flow>\n"

  let print_suggestion_header decl_file = 
    match decl_file with
      | None -> ()
      | Some f -> Printf.fprintf f "<declassifier-suggestions xmlns=\"http://openuri.org/declassifiers\">\n"

  let print_suggestion_footer decl_file =
    match decl_file with
      | None -> ()
      | Some f -> Printf.fprintf f "</declassifier-suggestions>\n"

  let print_decl_header decl_file =
    match decl_file with
      | None -> ()
      | Some f -> Printf.fprintf f "\t\t<suggestion>\n"

  let print_decl_footer decl_file =
    match decl_file with
      | None -> ()
      | Some f -> Printf.fprintf f "\t\t</suggestion>\n"
	  
  let sanitize_for_xml_output s = 
    let ltRegexp = Str.regexp "<" and
	gtRegexp = Str.regexp ">" and
	ampRegexp = Str.regexp "&" and
	quoteRegexp = Str.regexp "\"" in
      Str.global_replace ltRegexp "#lt" (Str.global_replace gtRegexp "#gt" (Str.global_replace ampRegexp "#amp" (Str.global_replace quoteRegexp "" s)))

  let output_declassifier decl_file = 
    let regexp = Str.regexp ("\\(.*\\):\\([0-9]+\\)\\(-\\([0-9]+\\)\\)?,\\([0-9]+\\)\\(-\\([0-9]+\\)\\)?") in
      fun expStr ->
	fun postStr ->
	match decl_file with
	  | None -> ()
	  | Some f -> 
	      if not (Str.string_match regexp postStr 0) then
		raise (Failure "could not match declassifier position!");
	      let pathname = Str.matched_group 1 postStr in
	      let lineStart = Str.matched_group 2 postStr in
	      let lineEnd = wrap_not_found (fun _ -> Str.matched_group 4 postStr) in
	      let columnStart = Str.matched_group 5 postStr in
	      let columnEnd = wrap_not_found (fun _ -> Str.matched_group 7 postStr) in
	      let filename = Str.global_replace (Str.regexp ".*/") "" pathname in
		Printf.fprintf f "\t\t\t<decl exp=\"%s\" path=\"%s\" file=\"%s\" lineStart=\"%s\" lineEnd=\"%s\" columnStart=\"%s\" columnEnd=\"%s\"/>\n"
		  (sanitize_for_xml_output expStr)
		  pathname
		  filename
		  lineStart
		  (match lineEnd with None -> lineStart | Some s -> s)
		  columnStart
		  (match columnEnd with None -> columnStart | Some s -> s)
end

let prune_graph graph s vl =
  let returnGraph = FlowGraph.create ~size:(FlowGraph.nb_vertex graph) () in
  let tSet = List.fold_left (fun soFar (s1,id1) -> FlowGraph.VertexSet.add (FlowGraph.GraphLabel.tagForNode (Label id1)) soFar) FlowGraph.VertexSet.empty vl in
  let nodes_on_source_to_sink = ref (FlowGraph.VertexSet.empty) and
      nodes_on_sink_to_source = ref (FlowGraph.VertexSet.empty) and
      visitAndAddToSet set v = (set := FlowGraph.VertexSet.add v (!set)) in
    FlowGraph.DFS.prefix_component
      (visitAndAddToSet nodes_on_source_to_sink)
      graph
      s;
    if FlowGraph.VertexSet.is_empty (FlowGraph.VertexSet.inter tSet !nodes_on_source_to_sink) then
      begin
	None
      end
    else
      begin
	let mirror_graph = Enumerater.OPER.mirror graph in
	  FlowGraph.VertexSet.iter (fun t -> 
		       if (FlowGraph.mem_vertex mirror_graph t) then
			 begin
			   FlowGraph.DFS.prefix_component
			     (visitAndAddToSet nodes_on_sink_to_source)
			     mirror_graph
			     t
			 end)
	    tSet;
	  let is_atom_to_include v tag = 
	    match v with
	      | Label n -> (tag = s) || (FlowGraph.VertexSet.mem tag tSet)
	      | _ -> true in
	    FlowGraph.iter_vertex (fun v -> 
				     if (FlowGraph.VertexSet.mem v !nodes_on_source_to_sink) && 
				       (FlowGraph.VertexSet.mem v !nodes_on_sink_to_source) &&
				       (is_atom_to_include (FlowGraph.GraphLabel.nodeForTag v) v) then
					 begin
					   (*Printf.printf ("adding %s to pruned graph\n") (FlowGraph.v_to_string v);*)
					   FlowGraph.add_vertex returnGraph v
					 end
					   (*else
					     Printf.printf ("not including %s in pruned graph\n") (FlowGraph.v_to_string v)*))
	      graph;
	    FlowGraph.iter_edges_e (fun e ->
				      let v1 = FlowGraph.E.src e and
					  v2 = FlowGraph.E.dst e and
					  i = FlowGraph.E.label e in
					if (FlowGraph.mem_vertex returnGraph v1) && (FlowGraph.mem_vertex returnGraph v2) then
					  let srcNode = FlowGraph.GraphLabel.nodeForTag v1 in
					  let add_edge () = FlowGraph.add_edge_e returnGraph (FlowGraph.E.create v1 i v2) in
					    match srcNode with
					      | Label n -> 
						  if not (FlowGraph.VertexSet.mem v1 tSet) then
						    add_edge ()
						  (*else
						    Printf.printf ("removing edge outbound from %s\n") (FlowGraph.v_to_string v1)*)
					      | _ -> add_edge ())
	      graph;
	    Some returnGraph
      end

let num_candidate_declassifier_edges graph = 
  FlowGraph.fold_edges_e (fun (_,w,_) -> fun soFar -> if (w == FlowGraph.infinity_hack) then soFar else soFar + 1) graph 0

let prune_and_augment_graph graph s vl = 
  let tNode = Label (-1) in
  let maybe_pruned_graph = prune_graph graph s vl in
    match maybe_pruned_graph with
      | None -> None,0 
      | Some pruned_graph -> 
	  Printf.printf ("graph pruned successfully -- size %d vertices, %d edges (%d candidate declassifiers)\n") (FlowGraph.nb_vertex pruned_graph) (FlowGraph.nb_edges pruned_graph) (num_candidate_declassifier_edges pruned_graph); flush stdout;
	  FlowGraph.add_vertex pruned_graph (FlowGraph.GraphLabel.tagForNode tNode);
	  let tTag = FlowGraph.GraphLabel.tagForNode tNode in
	    List.iter
	      (fun (t,id) ->
		 (*Printf.printf ("augment graph with edge from LABEL %d to %d") id (-1);*)
		 FlowGraph.add_edge_e pruned_graph (FlowGraph.E.create (FlowGraph.GraphLabel.tagForNode (Label id)) (FlowGraph.infinity_hack) tTag))
	      vl;
	    let name = "test" in
	      FlowGraphDotOutput.output_graph (open_out (name ^ ".pruned.dot")) pruned_graph;
	      (if (!Simputil.output_dot) then
		 let _ = 
		   timeThunk 
		     (fun _ -> Sys.command (Printf.sprintf "dot -Tpng %s.pruned.dot > %s.pruned.png" name name))
		     (SimpTimer.record_time "dot output")
		 in
		   ());
	      Printf.printf ("graph augmented successfully\n"); flush stdout;
	      (Some pruned_graph,tTag)

let cutset_from_vertex_cut vset graph = 
  FlowGraph.fold_edges_e
    (fun edge -> fun set ->
       let src,dst = FlowGraph.E.src edge, FlowGraph.E.dst edge in
	 if (Enumerater.VS.mem src vset) && not (Enumerater.VS.mem dst vset) then
	   CutSet.add (CutSet.edge_to_cut_elem edge) set
	 else
	   set)
    graph
    CutSet.empty

let is_incoming_outgoing_pair v1 v2 = (FlowGraph.is_incoming_node v1) && (FlowGraph.is_outgoing_node v2) && (FlowGraph.id_for_node v1 == FlowGraph.id_for_node v2)
    
let print_candidate_declassifier_stats graph = 
  let (num_expr,candidate_decl) = 
    FlowGraph.fold_edges_e 
      (fun e -> fun (num_expr,num_candidates) ->
	 let v1 = FlowGraph.E.src e and
	     v2 = FlowGraph.E.dst e and
	     a = FlowGraph.E.label e in
	   if (FlowGraph.is_incoming_node v1 && FlowGraph.is_outgoing_node v2) then
	     match FlowGraph.GraphLabel.nodeForTag v1,FlowGraph.GraphLabel.nodeForTag v2 with
		 LVar (ExpLVar l1,t1),LVar (ExpLVar l2,t2) ->
		   if (l1 == l2) then
		     if (a == FlowGraph.infinity_hack) then
		       (num_expr + 1, num_candidates)
		     else
		       (num_expr + 1, num_candidates + 1)
		   else
		     (num_expr,num_candidates)
	       | _ -> (num_expr,num_candidates)
	   else
	     (num_expr,num_candidates))
      graph
      (0,0) in
    Printf.printf ("total expressions: %d\n") (num_expr);
    Printf.printf ("candidate declassifiers: %d\n") (candidate_decl);
    flush stdout

let apply_placement_policy congraph =
  let returnGraph = FlowGraph.create ~size:(FlowGraph.nb_vertex congraph) () in
    FlowGraph.iter_vertex (FlowGraph.add_vertex returnGraph) congraph;
    FlowGraph.iter_edges_e 
      (fun e ->
	 let v1 = FlowGraph.E.src e and
	     v2 = FlowGraph.E.dst e in
	   if (FlowGraph.is_incoming_node v1 && FlowGraph.is_outgoing_node v2) then
	     (* look up how we should treat v1 -> v2 *)
	     begin
	       (*Printf.printf ("edge %s to %s\n") (FlowGraph.v_to_string v1) (FlowGraph.v_to_string v2);*)
	       let nv_incoming = (FlowGraph.GraphLabel.nodeForTag v1) and
		   nv_outgoing = (FlowGraph.GraphLabel.nodeForTag v2) in
		 begin
		   let mnv = 
		     match (nv_incoming,nv_outgoing) with 
			 LVar(ExpLVar nv_inc,_),_ ->
			   Some nv_inc
		       | LVar(PCLVar pc,_),_ ->
			   Some ("pc" ^ (string_of_int pc))
		       | _ -> None
		   in
		     match mnv with
		       | Some nv -> (* apply policy *) 
			   begin
			     if (Hashtbl.mem XmlConstraintReader.nvToPosMap nv) then
			       let pos = (Hashtbl.find XmlConstraintReader.nvToPosMap nv) in 
			       let pref = Placepolicy.get_preference_for_pos pos in
				 match pref with 
				   | Some pf -> Printf.printf ("\tthere is a preference for this position %s -- %s\n") pos (Placepolicy.preference_to_string pf)
				   | None -> ()
			   end;
			   FlowGraph.add_edge_e returnGraph e
		       | None -> FlowGraph.add_edge_e returnGraph e
		 end
	     end
	   else
	     FlowGraph.add_edge_e returnGraph e)
      congraph;
    returnGraph

let aggressively_cluster_graph congraph s t vl filter_fn =
  let newClusterTable = Hashtbl.create (FlowGraph.nb_vertex congraph) in 
    FlowGraphDotOutput.output_graph (open_out ("preaggressive.dot")) congraph;
    FlowGraph.iter_vertex (fun v -> Hashtbl.replace newClusterTable v v) congraph;
    let rec is_keep_node a = match (FlowGraph.nodeForTag a) with 
	LVar (ExpLVar _,_) -> true 
      | Label _ -> true
      | _ -> let a_node = (Hashtbl.find newClusterTable a) in 
	  if (a == a_node) then
	    false 
	  else is_keep_node a_node in 
    let changed = ref true in
    let returnGraph = FlowGraph.create () in
    let incoming_for_outgoing v = List.hd (FlowGraph.pred congraph v) in
    let outgoing_for_incoming v = List.hd (FlowGraph.succ congraph v) in
    let all_entry_points_have_same_cluster v = 
      (*
      let entryPoints = List.map (Hashtbl.find newClusterTable) (FlowGraph.pred congraph v) in
	not (List.exists (fun a -> a != List.hd entryPoints) (List.tl entryPoints)) in
      *)
      (List.tl (FlowGraph.pred congraph v) == []) in
    let is_label v = (match (FlowGraph.nodeForTag v) with Label _ -> true | _ -> false) in
      while (!changed) do
	changed := false;
	FlowGraph.iter_edges_e 
	  (fun e ->
	      let src = FlowGraph.E.src e and
		  dst = FlowGraph.E.dst e in
		if (is_keep_node src && not (is_keep_node dst) && not (is_label src)) then
		  begin
		    if (!Simputil.debug) then
		      Printf.printf ("FOUND CANDIDATE EDGE: %s to %s\n") (FlowGraph.v_to_string src) (FlowGraph.v_to_string dst);
		    if (all_entry_points_have_same_cluster dst) then
		      begin
			(* move dst into src's cluster *)
			Hashtbl.replace newClusterTable dst (Hashtbl.find newClusterTable src);
			if (!Simputil.debug) then
			  begin
			    Printf.printf ("ORIGINAL: %s to %s\n") (FlowGraph.v_to_string src) (FlowGraph.v_to_string dst);
			    Printf.printf ("\tCLUSTERED: %s moved into %s (%s)\n") (FlowGraph.v_to_string dst) (FlowGraph.v_to_string src) (FlowGraph.v_to_string (Hashtbl.find newClusterTable src))
			  end;
			changed := true
		      end
		  end
		else
		  ()
		    (*Printf.printf ("apparently don't care about (%s,%s)\n") (FlowGraph.v_to_string src) (FlowGraph.v_to_string dst)*)
	  )
	  congraph
      done;
      FlowGraph.iter_vertex (fun v -> if ((Hashtbl.find newClusterTable v) == v) then (FlowGraph.add_vertex returnGraph v)) congraph;
      FlowGraph.iter_edges_e 
	(fun e ->
	   let src = FlowGraph.E.src e and
	       dst = FlowGraph.E.dst e and
	       label = FlowGraph.E.label e in
	   let lookupSrc = Hashtbl.find newClusterTable src and
	       lookupDst = Hashtbl.find newClusterTable dst in
	     if (FlowGraph.is_incoming_node lookupSrc) && (outgoing_for_incoming lookupSrc == lookupDst) then
	       FlowGraph.add_edge_e returnGraph (FlowGraph.E.create lookupSrc label lookupDst)
	     else
	       let newSrc = let a = Hashtbl.find newClusterTable src in 
		 if (FlowGraph.is_incoming_node a) then 
		   outgoing_for_incoming a
		 else 
		   a and
		   newDst = let a = Hashtbl.find newClusterTable dst in 
		     if (FlowGraph.is_outgoing_node a) then 
		       incoming_for_outgoing a
		     else 
		       a in
		 if (newSrc != newDst) then
		   begin
		     FlowGraph.add_edge_e returnGraph (FlowGraph.E.create newSrc label newDst);
		     if (!Simputil.debug) then 
		       if (src == newSrc && dst = newDst) then 
			 Printf.printf ("ORIGINAL UNCHANGED: EDGE (%s,%s)\n") (FlowGraph.v_to_string newSrc) (FlowGraph.v_to_string newDst)
		       else 
			 Printf.printf ("CHANGED: EDGE (%s,%s)\n") (FlowGraph.v_to_string newSrc) (FlowGraph.v_to_string newDst)
		   end)
      congraph;
      returnGraph

let cluster_graph g s t vl filter_fn =
  let pre_clustered_graph = 
    let congraph = 
      if (!Simputil.aggressive_cluster) then 
	aggressively_cluster_graph g s t vl filter_fn
      else
	g
    in
      begin
	if (!Simputil.cluster) then 
	  let tSet = List.fold_right (FlowGraphDominators.VSet.add) (List.map (fun (t,id) -> (FlowGraph.GraphLabel.tagForNode (Label id))) vl) (FlowGraphDominators.VSet.empty) in
	    begin
	      (*Printf.printf ("clustering graph...\n");  flush stdout;*)
	      let pidom = 
		timeThunk 
		  (fun _ -> FlowGraphDominators.compute_immediate_dominators (Enumerater.OPER.mirror congraph) t (-2))
		  (SimpTimer.record_time "immediate dominators") in
		(*Printf.printf ("finished computing fast dominators\n");  flush stdout;*)
	      let incoming_for_outgoing v = List.hd (FlowGraph.pred congraph v) in
	      let outgoing_for_incoming v = List.hd (FlowGraph.succ congraph v) in
	      let is_label v = (match (FlowGraph.nodeForTag v) with Label _ -> true | _ -> false) in
	      let retGraph = 
		if (!Simputil.aggressive_cluster) then 
		  begin
		    let returnGraph = FlowGraph.create () in
		    let clusterTable = Hashtbl.create (FlowGraph.nb_vertex congraph) in
		    let numDominated = ref 0 in
		      FlowGraph.iter_vertex (fun v -> Hashtbl.replace clusterTable v v) congraph;
		      let changed = ref true in
			while !changed do
			  changed := false;
			  if (!Simputil.debug) then
			    Printf.printf "GOING AGAIN\n";
			  FlowGraph.iter_vertex (fun v ->
						   if (v != -2) && (Hashtbl.mem pidom v) && (Hashtbl.find pidom v) != -2 then 
						     begin
						       if (!Simputil.debug && (Hashtbl.mem pidom v) && (Hashtbl.find pidom v) != -2) then
							 Printf.printf ("CANDIDATE: %s immediately postdominated by %s (%s)\n") (FlowGraph.v_to_string v) (FlowGraph.v_to_string (Hashtbl.find pidom v)) (FlowGraph.v_to_string (Hashtbl.find clusterTable (Hashtbl.find pidom v)));
						       (*if Hashtbl.mem clusterTable (Hashtbl.find pidom v) then (* (FlowGraphDominators.VSet.exists filter_fn (pdom v)) then*)*)
						       let pidom_v = Hashtbl.find clusterTable (Hashtbl.find pidom v) in
							 if (filter_fn pidom_v) then
							   begin
							     if not (is_label v) &&
							       (not ((FlowGraph.is_outgoing_node pidom_v) && (incoming_for_outgoing pidom_v == v))) && 
							       (Hashtbl.find clusterTable v != pidom_v) then
								 begin
								   Hashtbl.replace clusterTable v pidom_v;
								   changed := true;
								   if (!Simputil.debug) then
								     Printf.printf ("CLUSTER: %s postdominated by %s\n") (FlowGraph.v_to_string v) (FlowGraph.v_to_string pidom_v);
								   if (FlowGraph.is_outgoing_node v) then 
								     let inc_node = incoming_for_outgoing v in
								       begin
									 Hashtbl.replace clusterTable inc_node pidom_v;	
									 if (!Simputil.debug) then
									   Printf.printf ("CLUSTER: %s postdominated by %s\n") (FlowGraph.v_to_string inc_node) (FlowGraph.v_to_string pidom_v);
									 numDominated := (!numDominated) + 1
								       end;
								       numDominated := (!numDominated) + 1
								 end
							     else if !Simputil.debug then
							       Printf.printf ("decided against postdominating %s with %s\n") (FlowGraph.v_to_string v) (FlowGraph.v_to_string pidom_v)
							   end
							 else if !Simputil.debug then
							   Printf.printf ("not filtered %s %d\n") (FlowGraph.v_to_string v) v;
						     end
						)
			    congraph
			done;
			Printf.printf ("%d nodes dominated away\n") (!numDominated);
			FlowGraph.iter_vertex (fun v -> if (Hashtbl.find clusterTable v) == v then FlowGraph.add_vertex returnGraph v) congraph;
			FlowGraph.iter_edges_e (fun e -> 
						  let src = FlowGraph.E.src e and 
						      dst = FlowGraph.E.dst e and 
						      label = FlowGraph.E.label e in
						    if (!Simputil.debug) then 
						      Printf.printf ("initially have edge %s,%s\n") (FlowGraph.v_to_string src) (FlowGraph.v_to_string dst);
						    let lookupSrc = Hashtbl.find clusterTable src and
							lookupDst = Hashtbl.find clusterTable dst in
						      if (FlowGraph.is_incoming_node lookupSrc) && (FlowGraph.is_outgoing_node lookupDst) && (lookupSrc == incoming_for_outgoing lookupDst) then
							begin
							  if (!Simputil.debug) then
							    Printf.printf ("AS IT SHOULD BE: connecting %s and %s\n") (FlowGraph.v_to_string lookupSrc) (FlowGraph.v_to_string lookupDst);
							  FlowGraph.add_edge_e returnGraph (lookupSrc,label,lookupDst)
							end
						      else
							let newSrc = if (FlowGraph.is_incoming_node lookupSrc) then outgoing_for_incoming lookupSrc else lookupSrc and
							    newDst = if (FlowGraph.is_outgoing_node lookupDst) then incoming_for_outgoing lookupDst else lookupDst in
							let weight = FlowGraph.infinity_hack in
							  if (newSrc != newDst) && not (FlowGraph.is_outgoing_node newSrc && incoming_for_outgoing newSrc == newDst) then
							    begin
							      FlowGraph.add_edge_e returnGraph (newSrc,weight,newDst);
							      if (!Simputil.debug) then
								Printf.printf ("EDGE FROM %s TO %s with weight %d\n") (FlowGraph.v_to_string newSrc) (FlowGraph.v_to_string newDst) weight
							    end
					       ) congraph;
			FlowGraphDotOutput.output_graph (open_out ("aggressive.before.dot")) congraph;
			FlowGraphDotOutput.output_graph (open_out ("aggressive.after.dot")) returnGraph;
			returnGraph
		  end
		else
		  begin
		    let pdom = timeThunk (fun _ ->  compute_dominators_from_idom congraph pidom) (SimpTimer.record_time "dominators") in
		    let returnGraph = FlowGraph.copy congraph in
		      FlowGraph.iter_vertex
			(fun v ->
			   if (FlowGraph.is_outgoing_node v) then 
			     let inc_v = incoming_for_outgoing v in
			       if (FlowGraphDominators.VSet.exists filter_fn (pdom v)) then
				 begin
				   (*let pidom_v = FlowGraphDominators.VSet.choose (FlowGraphDominators.VSet.filter filter_fn (pdom v)) in*)
				   (*Printf.printf ("clustering away %s -- postdominated by %s\n") (FlowGraph.v_to_string inc_v) (FlowGraph.v_to_string pidom_v);*)
				   FlowGraph.remove_edge returnGraph inc_v v;
				   FlowGraph.add_edge_e returnGraph (inc_v,FlowGraph.infinity_hack,v)
				 end
			       else if !Simputil.no_multiple_sources && (FlowGraphDominators.VSet.cardinal (FlowGraphDominators.VSet.inter (pdom v) (tSet)) == 0) then
				 begin
				   (*Printf.printf ("might want to cluster away expression %s as it flows many places -- [%s] vs [%s]\n") 
				     (FlowGraph.v_to_string v) 
				     (String.concat ";" (List.map (FlowGraph.v_to_string) (FlowGraphDominators.VSet.elements (pdom v))))
				     (String.concat ";" (List.map (FlowGraph.v_to_string) (FlowGraphDominators.VSet.elements tSet)));*)
				   FlowGraph.remove_edge returnGraph inc_v v;
				   FlowGraph.add_edge_e returnGraph (inc_v,FlowGraph.infinity_hack,v)
				 end
			)
			congraph;
		      returnGraph
		  end 
	      in
	      begin
		Printf.printf ("finished clustering\n");  flush stdout;
		DOT.output_graph (open_out ("compact.dot")) retGraph;
		retGraph
	      end
	    end
	else
	  congraph
      end
  in
    FlowGraphDotOutput.output_graph (open_out ("test.compact.dot")) pre_clustered_graph;
    (if (!Simputil.compact_graph) then
       (*match (prune_graph (Compactor.compact pre_clustered_graph (!Simputil.procedure_list)) s vl) with Some g -> g*)
       Compactor.compact pre_clustered_graph (!Simputil.procedure_list)
     else
       pre_clustered_graph)

let print_procedure_stats_for_flowgraph congraph = 
  let procedure_to_vertices_map = Hashtbl.create 100 in
  let add_vertex_to_procedure v p =
    Hashtbl.replace procedure_to_vertices_map p
      (FlowGraph.VertexSet.add v
	 (try 
	    (Hashtbl.find procedure_to_vertices_map p)
	  with Not_found ->
	    (FlowGraph.VertexSet.empty))
      ) in
    FlowGraph.iter_vertex 
      (fun v ->
	 match FlowGraph.procedure_for_node v with
	     Some proc -> add_vertex_to_procedure v proc
	   | None -> ())
      congraph;
    Hashtbl.iter 
      (fun k v ->
	 Printf.printf ("procedure %d: (%d; %d)\n") k (FlowGraph.VertexSet.cardinal v) 
	   (List.fold_left 
	      (fun n vert -> if (FlowGraph.is_outgoing_node vert || FlowGraph.is_incoming_node vert) then n + 1 else n) 
	      0 (FlowGraph.VertexSet.elements v)))
      procedure_to_vertices_map
	 

let propose_declassifiers_for_flowgraph congraph name lattice = 
  let incomparable_labels = LatticeGraph.get_incomparable_pairs lattice in
  let declassifier_file = 
   if (!Simp.output_declassifiers) then
      Some (open_out (name ^ ".declass.xml"))
    else
      None in
  let fca_file = 
   if (!Simputil.fca) then
      Some (open_out (name ^ ".fca.dot"))
    else
      None in
    DeclassifierOutput.print_suggestion_header declassifier_file;
    let total_suggestions = ref 0 in
      Printf.printf ("%d incomparable labels\n") (List.length incomparable_labels);
      List.iter (fun ((s1,id1),vl) ->	
		   Printf.printf ("--- %s ---\n") s1;
		   flush stdout;
		   try
		     let s = FlowGraph.GraphLabel.tagForNode (Label id1) in
		     let isExpressionNode v = 
		       match FlowGraph.GraphLabel.nodeForTag v with 
			 | (LVar (ExpLVar _,_)) -> true 
			 | _ -> false in
		     let _ = print_candidate_declassifier_stats congraph in
		     let (maybe_pruned_and_augmented_graph,superSink) = prune_and_augment_graph congraph s vl in
		       match maybe_pruned_and_augmented_graph with
		       | None -> ()
		       | Some pruned_and_augmented_graph ->
			   let clustered_graph_almost = timeThunk (fun _ -> cluster_graph (apply_placement_policy pruned_and_augmented_graph) s superSink vl isExpressionNode) (SimpTimer.record_time "cluster graph") in
			   let clustered_graph = (*filter_multiply_dominated_nodes s vl clustered_graph_almost in*) clustered_graph_almost in
			   let current_cut_num = ref 0 in
			   let lattice = FCA.new_lattice () in 
			   let associations = Hashtbl.create 100 in
			   let output_edgeset_from_vertexset vs = 
			     current_cut_num := (!current_cut_num) + 1;
			     total_suggestions := (!total_suggestions) + 1;
			     let cs = cutset_from_vertex_cut vs clustered_graph in
			       Printf.printf ("#%d:\n\t%s\n") 
				 (!current_cut_num) 
				 (String.concat "\n\t" (List.map CutSet.cut_to_string (CutSet.elements cs)));
			       flush stdout;
			       if (!Simputil.fca) then
				 begin
				   CutSet.iter 
				     (fun elem -> 
					if (Hashtbl.mem associations elem) then
					  Hashtbl.replace associations elem (FCA.AttrSet.add !current_cut_num (Hashtbl.find associations elem))
					else
					  Hashtbl.replace associations elem (FCA.AttrSet.singleton !current_cut_num))
				     cs
				 end;
			       DeclassifierOutput.print_decl_header declassifier_file;
			       DeclassifierOutput.print_decl_footer declassifier_file;
			       if (!current_cut_num > 1000) then
				 raise (Interrupt "exceeded maximum number of cuts (1000), terminating suggestion lister...")
			   in
			     if (FlowGraph.nb_vertex clustered_graph > 0) then
			       begin
				 let incomparable_labels = (String.concat "," (List.map fst vl)) in
				   Printf.printf ("--- %s ~> [%s] ---\n") s1 incomparable_labels;
				   Printf.printf ("graph: size %d vertices, %d edges (%d candidate declassifiers)\n") 
				     (FlowGraph.nb_vertex clustered_graph) 
				     (FlowGraph.nb_edges clustered_graph) 
				     (num_candidate_declassifier_edges clustered_graph); 
				   print_procedure_stats_for_flowgraph clustered_graph;
				   flush stdout;
				   DeclassifierOutput.print_flow_header declassifier_file s1 incomparable_labels;
				   if (!Simputil.lgf) then
				     output_graph_to_lgf clustered_graph (name ^ "." ^ (string_of_int !total_suggestions) ^ ".lgf") s superSink;
				   Enumerater.list_minimum_st_cuts clustered_graph s superSink output_edgeset_from_vertexset;
				   DeclassifierOutput.print_flow_footer declassifier_file;
				   if (!Simputil.fca) then
				     begin
				       Hashtbl.iter 
					 (fun e attr ->
					    let str = (CutSet.prune_cut (CutSet.cut_to_string e)) in 
					      Printf.printf ("%s is associated with %s\n") str (FCA.attrset_to_str attr);
					      FCA.add_new_association lattice str attr)
					 associations;
				       match fca_file with 
					 | Some f -> FCA.lattice_to_dot f lattice (!total_suggestions)
					 | _ -> ()  (* should never happen *)
				     end
			       end
			     else
			       Printf.printf ("graph is empty!\n")
		   with Interrupt s -> Printf.printf ("%s\n") s
		)
	incomparable_labels;
      print_dashed_line ();
      if (!Simputil.verbose) then
	begin
	  Printf.printf ("# suggestions: %d\n") (!total_suggestions);
	end;
      DeclassifierOutput.print_suggestion_footer declassifier_file


let propose_declassifiers c name lattice = 
  let congraph = command_to_flowgraph c name in
    propose_declassifiers_for_flowgraph congraph name lattice
