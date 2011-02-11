open Simpconsreader

module SimpGraph = 
  struct

    open Simp
    open Simputil
    open Graph

    module FlowGraph = struct
      
      module GraphLabel = struct
	type t = int
	let equal = (=)
	let hash = Hashtbl.hash
	let compare = compare

	let (nodeToTag : (lexp,int) Hashtbl.t) = Hashtbl.create 5000
	let (tagToNode : (int,lexp) Hashtbl.t) = Hashtbl.create 5000

	let currentNodeNumber = ref 0

	let tagForNode v = 
	    try
	      Hashtbl.find nodeToTag v 
	    with Not_found -> 
	      let rv = !currentNodeNumber in 
	      currentNodeNumber := (!currentNodeNumber) + 1;
	      Hashtbl.add nodeToTag v rv;
	      Hashtbl.add tagToNode rv v;
	      rv

	let nodeForTag x = 
	  try
	    Hashtbl.find tagToNode x
	  with
	    Not_found ->
	      begin
		Printf.printf ("about to die -- can't find tag for node %d\n") x;
		Hashtbl.find tagToNode x
	      end

	let string_of_graphlabel (n:t) = 
	  let v = nodeForTag n in
	    match v with 
	      | LVar (lv,tl) -> (atom_to_string v) ^ "\\n(" ^ String.concat ";" (List.map tag_to_string tl) ^ ")"
	      | _ -> (atom_to_string v)

      end

      let nodeForTag = GraphLabel.nodeForTag
      let tagForNode = GraphLabel.tagForNode

      module EdgeLabel = struct
	type t  = int
	let compare = compare
	let hash = Hashtbl.hash 
	let equal = (=)
	let default = 0
	  
	type label = t
	    
	let max_capacity x = x
	let min_capacity _ = 0
	let flow _ = 0
	  
	let zero = 0

	let add = (+)
	let sub = (-)
	let string_of_edgelabel = string_of_int

	let hack_infinity = 1000
      end
	
      let string_of_edge (v1,i,v2) =
	"(" ^ (GraphLabel.string_of_graphlabel v1) ^ 
	  "->(" ^ (EdgeLabel.string_of_edgelabel i) ^ ")->" ^ (GraphLabel.string_of_graphlabel v2) ^ ")"

      let v_to_string = GraphLabel.string_of_graphlabel
      let e_to_string = string_of_edge
      let edgelabel_to_string = EdgeLabel.string_of_edgelabel

      module G = Imperative.Digraph.ConcreteLabeled(GraphLabel)(EdgeLabel)
      module FF = Flow.Goldberg(G)(EdgeLabel)
      module VertexSet = Set.Make(struct type t = G.vertex let compare = compare end)
      module EdgeSet = Set.Make(struct type t = G.edge let compare = compare end)
      module Oper = Oper.I(G)
      module DFS = Traverse.Dfs(G)

      include G

      let currentNum = ref 0
      let atomToNum = Hashtbl.create 50

      (* TODO: actually use "infinity" as a value -- 
	 early attempts did not go well *)
      let infinity_hack = 1000

      let is_incoming_node a = 
	match (GraphLabel.nodeForTag a) with
	  | LVar (v,tl) -> List.mem `Incoming tl
	  | _ -> false

      let is_outgoing_node a = 
	match (GraphLabel.nodeForTag a) with
	  | LVar (v,tl) -> List.mem `Outgoing tl 
	  | _ -> false

      let id_for_lexp lexp =
	match lexp with
	  | LVar (v,tl) -> 
	      List.fold_left 
		(fun soFar -> 
		   fun t ->
		     match t with 
			 `UniqId s -> Some s
		       | _ -> soFar)
		None
		tl
	  | _ -> None

      let weight_for_lexp lexp =
	match lexp with
	  | LVar (v,tl) -> 
	      List.fold_left 
		(fun soFar -> 
		   fun t ->
		     match t with 
			 `Weight n -> Some n
		       | _ -> soFar)
		None
		tl
	  | _ -> None

      let procedure_for_lexp lexp = 
	match lexp with
	  | LVar (v,tl) -> 
	      List.fold_left 
		(fun soFar -> 
		   fun t ->
		     match t with 
			 `Procedure n -> Some n
		       | _ -> soFar)
		None
		tl
	  | _ -> None

      let procedure_for_node n = 
	let lexp = GraphLabel.nodeForTag n in
	  procedure_for_lexp lexp

      let id_for_node a = id_for_lexp (GraphLabel.nodeForTag a)

      let expstr_for_node a = 
	match a with
	  | LVar (v,tl) -> 
	      List.fold_left 
		(fun soFar -> 
		   fun t ->
		     match t with 
			 `ExpStr s -> Some s
		       | _ -> soFar)
		None
		tl
	  | _ -> None	

      let constraint_set_to_flowgraph cl lattice = 
	match cl with 
	  | [] -> G.create ()
	  | _  -> 
	      let atoms = timeThunk (fun _ -> atoms_in_conslist cl) (SimpTimer.record_time "get atoms in constaint list") in 
	      let _ = 
		begin
		  Printf.printf ("%d atoms\n") (LexpSet.cardinal atoms);
		  flush stdout
		end
	      in
	      let g = G.create ~size:(LexpSet.cardinal atoms) () in
	      let get_sub_lv_node s lexp =
		match lexp with 
		  | (LVar (lv,t)) -> LVar (lv,s :: t) 
		  | _ -> raise (Failure "cannot get sub lv node for non-lvar")
	      in
	      let get_incoming_lv_node = get_sub_lv_node `Incoming and
		  get_outgoing_lv_node = get_sub_lv_node `Outgoing in
	      let get_incoming_node a = 
		match a with 
		  | LVar (ExpLVar l,t) -> get_incoming_lv_node a
		  | _ -> a 
	      and
		  get_outgoing_node a = 
		match a with 
		  | LVar (ExpLVar l,t) -> get_outgoing_lv_node a
		  | _ -> a
	      in
		begin
		  timeThunk 
		    (fun _ ->
		  LexpSet.iter 
		    (function 
		       | LVar (l,t) -> 
			   (match l with 
			      | ExpLVar e -> 
				  let incoming_l = get_incoming_lv_node (LVar (l,t)) and
				      outgoing_l = get_outgoing_lv_node (LVar (l,t)) in 
				  let nodeId = id_for_lexp incoming_l in
				  let incoming_tag = GraphLabel.tagForNode incoming_l and
				      outgoing_tag = GraphLabel.tagForNode outgoing_l in
				    begin
				      (*Printf.printf ("incoming: %d, outgoing: %d\n") incoming_tag outgoing_tag;*)
				      timeThunk (fun _ -> (G.add_vertex g incoming_tag;
							   G.add_vertex g outgoing_tag))
					(SimpTimer.record_time ~silent:true "graph building (add_vertex)");
				      let edgeWeight = match nodeId with 
					| Some id ->
					    if (StringSet.mem id (!XmlConstraintReader.nvNoDeclassify)) then
					      infinity_hack
					    else
					      (match (weight_for_lexp (LVar (l,t))) with
						| None -> 1
						| Some n -> n)
					| None -> 1
				      in
					G.add_edge_e g (G.E.create incoming_tag edgeWeight outgoing_tag);
					(*Printf.printf("\tadded vertices to graph\n");
					  flush stdout;*) ()
				    end
			      | _ -> 
				  let lvar_tag = GraphLabel.tagForNode (LVar (l,t))
				  in
				    begin
				      timeThunk (fun _ -> G.add_vertex g lvar_tag) ((SimpTimer.record_time ~silent:true "graph building (add_vertex)"));
				      (*Printf.printf ("added tag for %s\n") (lexp_to_string (LVar (l,t)));
				      flush stdout;*) ()
				    end
			   )
		       | Label n -> 
			   let lab_tag = GraphLabel.tagForNode (Label n)
			   in
			     G.add_vertex g lab_tag
		       | Join (_,_) -> raise (Failure "graph contains non-atomic node"))
		    atoms)
		    (SimpTimer.record_time "building graph (add nodes)");
		  Printf.printf ("added each atom to the graph as a node -- graph size %d nodes\n") (G.nb_vertex g);
		  flush stdout;
		  timeThunk 
		    (fun _ -> 
		      List.iter
			(fun (Leq (le,rhsA)) ->
			  (* add variable connections -- note that don't care if something flows to top or from bottom! *)
			  let lhsAtoms = atoms_in_lexp le in
			  LexpSet.iter 
			    (fun a ->
			      let add_edge_thunk = 
				fun _ -> 
				  let e = G.E.create
				      (GraphLabel.tagForNode (get_outgoing_node a)) 
				      (infinity_hack) 
				      (GraphLabel.tagForNode (get_incoming_node rhsA))
				  in
				  (*Printf.printf ("edge: (%s,%s)\n\tconstraint: %s\n") (lexp_to_string a) (lexp_to_string rhsA) (cons_to_string (Leq (le,rhsA)));*)
				  G.add_edge_e g e 
			      in
			      match a with
			      | Label id -> if (LatticeGraph.is_bottom lattice id) then () else add_edge_thunk ()
			      | _ -> add_edge_thunk ())
			    lhsAtoms)
			cl)
		    (SimpTimer.record_time "building graph (add edges)");
		  Printf.printf ("added edges between each atom to the graph -- graph size %d vertices, %d edges\n") (G.nb_vertex g) (G.nb_edges g);
		  flush stdout;
		  g
		end

      module TagSet = Set.Make(
	struct 
	  type t = G.vertex
	  let compare = compare 
	end)

      open Graphviz.DotAttributes
      
      let edge_attributes e = 
	match e with 
	    (v1,i,v2) ->
	      [`Label ("(" ^ 
			 (string_of_int i) ^ 
			 ")")]

      let default_edge_attributes _ = []

      let rec vertex_name a = 
	try 
	  let atom_name = (Hashtbl.find atomToNum a) in
	  "node" ^ (string_of_int atom_name)
	with Not_found ->
	  currentNum := (!currentNum) + 1;
	  Hashtbl.add atomToNum a (!currentNum);
	  vertex_name a

      let vertex_attributes a = 
	let color = 
	  match (GraphLabel.nodeForTag a) with
	    | Label n ->  [`Fontcolor 0xFFFFFF;`Style `Filled;`Fillcolor 0x0000FF]
	    | _ -> [] in
	  color @ [`Label (GraphLabel.string_of_graphlabel a)]

      let default_vertex_attributes _ = []
      let graph_attributes _ = []

      let get_subgraph _ = None
    end
      
    module FlowGraphDotOutput = Graphviz.Dot(FlowGraph)

    let output_graph_to_lgf congraph fileName s t = 
      let out_stream = open_out fileName in
      let r = ref 0 in
	Printf.fprintf out_stream "@nodes\n";
	Printf.fprintf out_stream "label\tstring\n";
	FlowGraph.iter_vertex 
	  (fun v ->
	     Printf.fprintf out_stream "%d\t\"%s\"\n" v (String.escaped (FlowGraph.v_to_string v)))
	  congraph;
	Printf.fprintf out_stream "@arcs\n";
	Printf.fprintf out_stream "\t\tlabel\tcapacity\tstring\n";
	FlowGraph.iter_edges_e
	  (fun e ->
	     let v1 = FlowGraph.E.src e and
		 v2 = FlowGraph.E.dst e and
		 w = FlowGraph.E.label e in
	       Printf.fprintf out_stream "%d\t%d\t%d\t%d\t\"%s\"\n"
		 v1
		 v2
		 (!r)
		 w
		 (String.escaped (FlowGraph.e_to_string e));
	  r := (!r) + 1)
	  congraph;
	Printf.fprintf out_stream "@attributes\n";
	Printf.fprintf out_stream "source %d\n" s;
	Printf.fprintf out_stream "target %d\n" t;
	close_out out_stream


  end
