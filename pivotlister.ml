open Simputil
open Simpgraph.SimpGraph

module type PIVOT_DEBUG =
sig
  include Graph.Sig.I

  val v_to_string : V.t -> string
  val e_to_string : E.t -> string
  val edgelabel_to_string : E.label -> string
end

module EnumerateCuts =
  functor (G : PIVOT_DEBUG) ->
    functor (F : sig 
	       include Graph.Flow.FLOW with type label = G.E.label and type t = int
	       val hack_infinity : int
	     end) ->
struct
  open Graph
    
  module EdgeSet = Set.Make(struct type t = G.E.t let compare = compare end)
  module VertexSet = 
    functor (G : PIVOT_DEBUG) ->
  struct 
    include Set.Make(
      struct type t = G.V.t 
	     let compare = compare 
      end)
      
    let string_of_set s = (String.concat ";" (List.map G.v_to_string (elements s)))
  end

  module VS = VertexSet(G)
  module FF = Graph.Flow.Ford_Fulkerson(G)(F)
  module DFS = Graph.Traverse.Dfs(G)
  module SCC = Graph.Components.Make(G)
  module OPER = Graph.Oper.I(G)

  module Weight = struct
    type t = F.t
    type label = F.label
    let weight = F.max_capacity
    let compare = F.compare
    let add = F.add
    let zero = F.zero
  end

  module PATH = Graph.Path.Dijkstra(G)(Weight) 

  module Int = struct 
    type t = int 
    let compare = compare 
    let hash = Hashtbl.hash 
    let equal = (=)
    let default = 0
  end

  module SuperGraph = struct
    include Graph.Imperative.Digraph.ConcreteLabeled(Int)(Int)
    let v_to_string = string_of_int
    let e_to_string e = (v_to_string (E.src e)) ^ "->" ^ (v_to_string (E.dst e))
    let edgelabel_to_string = string_of_int
  end

  module SUPER_OPER = Graph.Oper.I(SuperGraph)
  module SUPER_DFS = Graph.Traverse.Dfs(SuperGraph)
  module SuperVS = VertexSet(SuperGraph)
  module FasterTransitiveClosure = Transitiveclosure.TransitiveClosure(SuperGraph)

  let rec fold_int f a n = 
    match n with 
      | 0 -> a
      | _ -> fold_int f (f a n) (n - 1)

  let build_inverse_residual_graph graph new_flow = 
    let inv_residual_graph = G.create ~size:(G.nb_vertex graph) () in
      G.iter_vertex (G.add_vertex inv_residual_graph) graph;
      G.iter_edges_e 
	(fun e -> 
	   if (F.compare (new_flow e) (F.zero) = 1) then 
	     begin
	       (*Printf.printf ("flow at edge %s is %d, so edge goes in inverse residual graph\n") 
		 (G.e_to_string e)
		 (new_flow e)
	       ;*)
	       G.add_edge_e inv_residual_graph e
	     end;
	   (*
	     Printf.printf ("edgelabel: %d vs flow %d\n") 
	     (int_of_string (G.edgelabel_to_string (G.E.label e)))
	     (new_flow e)
	   ;
	   *)
	   if (F.compare (new_flow e) (F.max_capacity (G.E.label e)) = -1) then
	     begin
	       (*Printf.printf ("flow at edge %s is not saturated, so reverse edge goes in inverse residual graph\n") (G.e_to_string e);*)
	       G.add_edge inv_residual_graph (G.E.dst e) (G.E.src e);
	     end)
	graph;
      inv_residual_graph

  let valid_edges graph edge_flow = 
    G.fold_edges_e 
      (fun edge ->
	 fun es -> 
	   let v1,v2 = G.E.src edge, G.E.dst edge in
	   let newFlow = edge_flow edge in
	     if (newFlow > 0) then
	       EdgeSet.add (G.E.create v1 (G.E.label edge) v2) es
	     else
	       es)
      graph
      EdgeSet.empty

  let valid_vertices_from_valid_edges ve = 
    EdgeSet.fold
      (fun e vs -> VS.add (G.E.src e) (VS.add (G.E.dst e) vs))
      ve
      VS.empty

(*
	     Printf.printf "(%s,%s) originally has flow %s, now has flow %d\n"
	       (G.v_to_string v1)
	       (G.v_to_string v2)
	       (G.edgelabel_to_string (G.E.label edge))
	       (edge_flow edge) *)
(*
  let pivot s_set t_set graph s t valid_pivots = 
    let mirror_g = OPER.mirror graph in
    let rec select_pivot s_set t_set = 
      (* candidate pivot: anything in graph that's not in t_set *)
      if (VS.is_empty s_set) then
	begin
	  if (VS.mem s t_set) then
	    (None,VS.empty)
	  else
	    (Some s,VS.add s VS.empty)
	end
      else
	let diff = VS.diff (VS.diff valid_pivots s_set) t_set in
	  if (VS.is_empty diff) then
	    (None,VS.empty)
	  else
	    let candidate = List.hd (VS.elements diff) in
	      (*Printf.printf ("considering candidate %s\n") (G.v_to_string candidate);*)
	      (* check if the reachability set for candidate intersects t_set *)
	    let vs = ref VS.empty in 
	      DFS.prefix_component (fun v -> vs := VS.add v (!vs)) mirror_g candidate;
	      let candidate_set = VS.diff (!vs) s_set in
		if (VS.is_empty (VS.inter candidate_set t_set)) then
		  (Some candidate,candidate_set) 
		else
		  select_pivot s_set (VS.add candidate t_set)
    in
      select_pivot s_set t_set
*)

  let super_transitive_closure graph = 
    FasterTransitiveClosure.transitive_closure graph

  let create_preprocessed_graph graph valid_pivots = 
    let isactive_table = Hashtbl.create 100 in
    let (num_sccs,scc_fn) = SCC.scc graph in
    let scc_graph = 
      let the_graph = SuperGraph.create ~size:(G.nb_vertex graph) () in
	for i = 0 to (num_sccs - 1) do
	  SuperGraph.add_vertex the_graph i;
	  Hashtbl.add isactive_table i false
	done;
	G.iter_edges
	  (fun v1 v2 -> 
	     if (scc_fn v1) != (scc_fn v2) then
	       begin
		 SuperGraph.add_edge the_graph (scc_fn v1) (scc_fn v2);
		 (*Printf.printf ("adding edge from %d (%s) to %d (%s)\n")
		   (scc_fn v1)
		   (G.v_to_string v1)
		   (scc_fn v2)
		   (G.v_to_string v2);*)
		 ()
	       end)
	  graph;
	the_graph
    in
      if (!Simputil.verbose) then
	begin
	  Printf.printf "about to perform transitive closure... scc graph has size %d\n" (SuperGraph.nb_vertex scc_graph);
	  flush stdout
	end;
      (*for i = 0 to (SuperGraph.nb_vertex scc_graph - 1) do
	for j = 0 to (SuperGraph.nb_vertex scc_graph - 1) do
	  if (SuperGraph.mem_edge scc_graph i j) then
	    Printf.printf ("(%d,%d) ") i j
	done
      done;
      Printf.printf ("\n");*)
      (*let tc_graph = timeThunk (fun _ -> SUPER_OPER.transitive_closure scc_graph) (SimpTimer.record_time "SCC transitive closure") in*)
      let tc_graph = timeThunk (fun _ -> super_transitive_closure scc_graph) (SimpTimer.record_time "SCC transitive closure") in
	if (!Simputil.verbose) then
	  begin
	    Printf.printf "transitive closure finished\n";
	    flush stdout
	  end;
	G.iter_vertex
	  (fun v -> 
	     if (VS.mem v valid_pivots) then
	       Hashtbl.replace isactive_table (scc_fn v) true)
	  graph;
	let tc_active_graph = SuperGraph.create ~size:(SuperGraph.nb_vertex tc_graph) () in
	let removeSet = 
	  Hashtbl.fold 
	    (fun key value set ->
	       if (value = false) then
		 SuperVS.add key set
	       else
		 set)
	    isactive_table
	    SuperVS.empty in
	  SuperGraph.iter_vertex 
	    (fun v ->
	       if not (SuperVS.mem v removeSet) then
		 SuperGraph.add_vertex tc_active_graph v)
	    tc_graph;
	  SuperGraph.iter_edges_e 
	    (fun (v1,i,v2) ->
	       if not (SuperVS.mem v1 removeSet) && not (SuperVS.mem v2 removeSet) then
		 SuperGraph.add_edge_e tc_active_graph (v1,i,v2))
	    tc_graph;
	  (*
	    Hashtbl.iter 
	    (fun key value -> 
	    if (value = false) then
	    begin
	    SuperGraph.remove_vertex tc_active_graph key;
	  (*Printf.printf "\tremoving vertex %s from graph, as it is not active\n" (SuperGraph.v_to_string key);*)
	    ()
	    end)
	    isactive_table)*)
	;
	(scc_fn,scc_graph,tc_graph,tc_active_graph)

  exception Interrupt

  let pivot s_set t_set graph tc_graph tc_active_graph scc_fn s t = 
    (* M_0 can be found by removing vertices of indegree 0 in G_3, 
       and updating the indegrees of the remaining vertices of G_3 *)
    (* choose any pivot element in M_0 - T_0 that is not 
       already in s_set or t_set *)
    (* remove all vertices from tc_active_graph that are already in s_set *)
    (*Printf.printf ("find pivot -- S: [%s] T: [%s]\n")
      (SuperVS.string_of_set s_set)
      (SuperVS.string_of_set t_set);*)
    if (SuperVS.is_empty s_set) then
      let s_scc = scc_fn s in
	if (SuperVS.mem s_scc t_set) then
	  (None,SuperVS.empty)
	else
	  (Some (scc_fn s), SuperVS.singleton (scc_fn s))
    else
      let minset_graph = SuperGraph.copy tc_active_graph in
      let remove_component v = SuperGraph.remove_vertex minset_graph v in
	SuperVS.iter remove_component s_set;
	SuperVS.iter remove_component t_set;
	(* any vertex with indegree 0 *)
	let candidates = 
	  SuperGraph.fold_vertex 
	    (fun sv set ->
	       if (SuperGraph.in_degree minset_graph sv = 0) then
		 begin
		   (*Printf.printf "\t%s is in the minimum set\n" (SuperGraph.v_to_string sv);*)
		   let hasPredInTSet = 
		     try 
		       SuperGraph.iter_pred 
			 (fun v ->
			    if (SuperVS.mem v t_set) then
			      begin
				(*Printf.printf "\tbut has a predecessor in t_set -- %s\n" (SuperGraph.v_to_string v);*)
				raise Interrupt
			      end)
			 tc_active_graph
			 sv;
			 false
		     with
			 Interrupt -> true
		   in
		     if (hasPredInTSet) then
		       set
		     else
		       SuperVS.add sv set
		 end
	       else
		 set)
	    minset_graph
	    SuperVS.empty
	in
	  if (SuperVS.is_empty candidates) then
	    (None,SuperVS.empty)
	  else
	    let sv = (SuperVS.choose candidates) in
	    let reachset = 
	      List.fold_left 
		 (fun set v -> SuperVS.add v set)
		 SuperVS.empty
		 (sv :: (SuperGraph.pred tc_graph sv))
	    in
	      (*Printf.printf ("\treach set is [%s]\n") (SuperVS.string_of_set reachset);*)
	      (Some sv,reachset)
(*
  let rec list_sets s_set t_set graph s t valid_pivots cut_function = 
    (*Printf.printf ("list([%s],[%s])\n") (VS.string_of_set s_set) (VS.string_of_set t_set);*)
    let (pv,pivot_set) = pivot s_set t_set graph s t valid_pivots in
    let output_cut () = Printf.printf ("list (%s,%s) --> cut: [%s]\n") (VS.string_of_set s_set) (VS.string_of_set t_set) (VS.string_of_set s_set) in
      if (VS.is_empty pivot_set) then
	cut_function s_set
      else
	match pv with 
	    None ->
	      cut_function s_set
	  | Some v ->
	      begin
		(*Printf.printf ("s_set: %s, t_set: %s, pivot: %s, pivot set: [%s]\n") 
		  (VS.string_of_set s_set)
		  (VS.string_of_set t_set)
		  (G.v_to_string v)
		  (VS.string_of_set pivot_set);*)
		list_sets s_set (VS.add v t_set) graph s t valid_pivots cut_function;
		list_sets (VS.union pivot_set s_set) t_set graph s t valid_pivots cut_function
	      end
*)

  let build_inverse_scc_fn graph scc_fn num_sccs = 
    let underlying_tbl = Hashtbl.create num_sccs in
      for i = 0 to (num_sccs - 1) do
	Hashtbl.add underlying_tbl i VS.empty
      done;
      G.iter_vertex
	(fun v ->
	   let scc_v = scc_fn v in
	   let current_set = Hashtbl.find underlying_tbl scc_v in
	     Hashtbl.replace underlying_tbl scc_v (VS.add v current_set))
	graph;
      Hashtbl.find underlying_tbl

  let rec list_sets s_set t_set graph s t valid_pivots cut_function = 
    let (scc_fn,scc_graph,tc_graph,tc_active_graph,inverse_scc_fn) = 
      timeThunk 
	(fun _ ->
	   let (scc_fn,scc_graph,tc_graph,tc_active_graph) = create_preprocessed_graph graph valid_pivots in
	   let inverse_scc_fn = build_inverse_scc_fn graph scc_fn (SuperGraph.nb_vertex scc_graph)
	   in
	     (scc_fn,scc_graph,tc_graph,tc_active_graph,inverse_scc_fn))
	(SimpTimer.record_time "enumeration preprocessing")
    in
    let apply_cut_function scc_set = 
      if not (SuperVS.is_empty scc_set) then
	cut_function
	  (SuperVS.fold
	     (fun scc vSet ->
		VS.union (inverse_scc_fn scc) vSet)
	     scc_set
	     VS.empty)
    in
    let rec list_sets_helper s_set t_set = 
      (*Printf.printf ("list([%s],[%s])\n") (SuperVS.string_of_set s_set) (SuperVS.string_of_set t_set);*)
      let (pv,pivot_set) = pivot s_set t_set graph tc_graph tc_active_graph scc_fn s t in
	if (SuperVS.is_empty pivot_set) then
	  apply_cut_function s_set
	else
	  match pv with 
	      None ->
		apply_cut_function s_set
	    | Some v ->
		begin
		  list_sets_helper s_set (SuperVS.add v t_set);
		  list_sets_helper (SuperVS.union pivot_set s_set) t_set
		end
    in
      timeThunk 
	(fun _ ->
	   list_sets_helper s_set (SuperVS.add (scc_fn t) t_set))
	(SimpTimer.record_time "enumerate cuts")	     

  let list_minimum_st_cuts graph s t cut_function = 
    (* 1) first find max from from s to t in graph 
       2) construct G^*, the inverse residual graph
    *)
    let (new_flow,flow_value) =  
      timeThunk 
	(fun _ ->
	   if (!Simputil.verbose) then
	     begin
	       Printf.printf "determining cut... graph is size %d\n" (G.nb_vertex graph);
	       flush stdout
	     end;
	   if (G.is_empty graph) then
	     ((fun _ -> F.zero), F.zero)
	   else
	     FF.maxflow graph s t)
	(SimpTimer.record_time "determine maximum flow")
    in
      if (flow_value >= F.hack_infinity && false) then
	begin
	  if (!Simputil.verbose) then
	    begin
	      Printf.printf "finished determining cut -- flow value %d > F.hack_infinity, stopping\n" flow_value;
	      flush stdout;
	      let bad_graph = G.create ~size:(G.nb_vertex graph) () in
 		G.iter_vertex (fun v -> G.add_vertex bad_graph v) graph;
		G.iter_edges_e 
		  (fun e -> 
		     if (F.max_capacity (G.E.label e)) == F.hack_infinity then
		       begin
			 Printf.printf ("(%s,%s) is an uncuttable edge\n") (G.v_to_string (G.E.src e)) (G.v_to_string (G.E.dst e));
			 G.add_edge_e bad_graph e
		       end)
		  graph
		;
		let (bad_path,weight) = PATH.shortest_path bad_graph s t in
		  List.iter 
		    (fun e ->
		       let src = G.E.src e and
			   dst = G.E.dst e in
			 if (G.mem_vertex graph src) && (G.mem_vertex graph dst) then
			   begin
			     Printf.printf ("%s --> %s\n") (G.v_to_string (G.E.src e)) (G.v_to_string (G.E.dst e));
			     flush stdout
			   end
		    ) bad_path;
		()
	    end
	end
      else
	begin
	  if (!Simputil.verbose) then 
	    begin
	      Printf.printf "finished determining cut -- flow value %d\n" flow_value; 
	      flush stdout
	    end;
	  if (flow_value = 0) then
	    ()
	  else
	    let inverse_residual_graph = build_inverse_residual_graph graph new_flow in
	    let vv = valid_vertices_from_valid_edges (valid_edges graph new_flow) in
	      (*Printf.printf ("flow value: %d\n") flow_value;
		Printf.printf ("valid vertices: [%s]\n") (VS.string_of_set vv);*)
	      (*list_sets VS.empty VS.empty inverse_residual_graph s t (VS.remove t vv) cut_function*)
	      list_sets SuperVS.empty SuperVS.empty 
		inverse_residual_graph s t (VS.remove t vv) cut_function
	end
end 

module Int = struct 
  type t = int 
  let compare = compare 
  let hash = Hashtbl.hash 
  let equal = (=)
  let default = 0
end

module TestGraph = 
struct
  include Graph.Imperative.Digraph.ConcreteLabeled(Int)(Int)

  let v_to_string v = string_of_int (V.label v)
  let edgelabel_to_string el = (string_of_int el)
  let e_to_string e = (v_to_string (E.src e)) ^ "->" ^ (v_to_string (E.dst e))
end

module F = struct
  type label = int
  type t = int
  let max_capacity x = x
  let min_capacity _ = 0
  let flow _ = 0
  let add = (+)
  let sub = (-)
  let compare = compare
  let zero = 0
  let hack_infinity = 100
end

module EnumerateTester = EnumerateCuts(TestGraph)(F)

(*
let testGraph = TestGraph.create ()
let testGraph2 = TestGraph.create ()
let testGraph3 = TestGraph.create ()
let testGraph4 = TestGraph.create ()
let testGraph5 = TestGraph.create ()
let testGraph6 = TestGraph.create ()
let testGraph7 = TestGraph.create ()
let testGraph8 = TestGraph.create ()
let testGraph9 = TestGraph.create ()
let testGraph10 = TestGraph.create ()
let testGraph11 = TestGraph.create ()
let testGraph12 = TestGraph.create ()
let testGraph13 = TestGraph.create ()
let _ = 
  begin
(*
    TestGraph.add_vertex testGraph 0;
    TestGraph.add_vertex testGraph 1;
    TestGraph.add_vertex testGraph 2;
    TestGraph.add_vertex testGraph 3;
    TestGraph.add_vertex testGraph 4;
    TestGraph.add_vertex testGraph 5;
    TestGraph.add_edge_e testGraph (0,1,1);
    TestGraph.add_edge_e testGraph (1,3,2);
    TestGraph.add_edge_e testGraph (2,1,4);
    (*TestGraph.add_edge_e testGraph (1,1,3);
    TestGraph.add_edge_e testGraph (3,5,4);*)
    TestGraph.add_edge_e testGraph (4,1,5);
*)
    TestGraph.add_vertex testGraph 0;
    TestGraph.add_vertex testGraph 1;
    TestGraph.add_vertex testGraph 2;
    TestGraph.add_vertex testGraph 3;
    TestGraph.add_vertex testGraph 10;
    TestGraph.add_vertex testGraph 11;
    TestGraph.add_vertex testGraph 12;
    TestGraph.add_vertex testGraph 13;
    TestGraph.add_edge_e testGraph (0,1,1);
    TestGraph.add_edge_e testGraph (0,1,2);
    TestGraph.add_edge_e testGraph (1,1,3);
    TestGraph.add_edge_e testGraph (2,1,3);

    TestGraph.add_edge_e testGraph (1,1,10);
    TestGraph.add_edge_e testGraph (1,1,11);
    TestGraph.add_edge_e testGraph (1,1,12);
    TestGraph.add_edge_e testGraph (1,1,13);

    TestGraph.add_edge_e testGraph (10,1,2);
    TestGraph.add_edge_e testGraph (11,1,2);
    TestGraph.add_edge_e testGraph (12,1,2);
    TestGraph.add_edge_e testGraph (13,1,2);

    TestGraph.add_vertex testGraph2 0;
    TestGraph.add_vertex testGraph2 1;
    TestGraph.add_vertex testGraph2 2;
    TestGraph.add_vertex testGraph2 3;
    TestGraph.add_vertex testGraph2 4;
    TestGraph.add_vertex testGraph2 5;
    TestGraph.add_vertex testGraph2 6;
    TestGraph.add_vertex testGraph2 7;

    TestGraph.add_edge_e testGraph2 (0,1,1);
    TestGraph.add_edge_e testGraph2 (0,1,2);
    TestGraph.add_edge_e testGraph2 (1,1,3);
    TestGraph.add_edge_e testGraph2 (3,1,5);
    TestGraph.add_edge_e testGraph2 (1,1,2);
    TestGraph.add_edge_e testGraph2 (5,1,7);
    TestGraph.add_edge_e testGraph2 (2,1,4);
    TestGraph.add_edge_e testGraph2 (4,1,6);
    TestGraph.add_edge_e testGraph2 (6,1,7);

    TestGraph.add_vertex testGraph3 0;
    TestGraph.add_vertex testGraph3 1;
    TestGraph.add_vertex testGraph3 2;
    TestGraph.add_vertex testGraph3 3;
    TestGraph.add_edge_e testGraph3 (0,1,1);
    TestGraph.add_edge_e testGraph3 (1,10,2);
    TestGraph.add_edge_e testGraph3 (2,1,3);

    TestGraph.add_vertex testGraph4 0;
    TestGraph.add_vertex testGraph4 1;
    TestGraph.add_vertex testGraph4 2;
    TestGraph.add_vertex testGraph4 3;
    TestGraph.add_vertex testGraph4 5;
    TestGraph.add_vertex testGraph4 6;
    
    TestGraph.add_edge_e testGraph4 (0,100,1);
    TestGraph.add_edge_e testGraph4 (1,1,2);
    TestGraph.add_edge_e testGraph4 (2,100,3);
    TestGraph.add_edge_e testGraph4 (3,100,4);
    TestGraph.add_edge_e testGraph4 (0,100,5);
    TestGraph.add_edge_e testGraph4 (5,1,6);
    TestGraph.add_edge_e testGraph4 (6,100,4);
    TestGraph.add_edge_e testGraph4 (4,100,7);



    Printf.printf ("bork!\n");
    (*EnumerateTester.list_minimum_st_cuts testGraph 0 3*)
  (* EnumerateTester.list_minimum_st_cuts testGraph2 0 7*)
    
    EnumerateTester.list_minimum_st_cuts testGraph4 0 7
(*
      (fun s_set -> 
	 Printf.printf ("[%s]\n") 
	   (EnumerateTester.VS.string_of_set s_set)) 
*)
      (fun s_set -> 
	 Printf.printf ("[%s]\n") 
	   (EnumerateTester.VS.string_of_set s_set)) 
  end
*)
