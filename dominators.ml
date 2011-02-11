open Graph
open Simpgraph.SimpGraph

module Dominators = functor (G : Graph.Sig.I) ->
struct

  module VSet = Set.Make(struct type t = G.vertex let compare = compare end)
  module Oper = Oper.I(G)
  module Components = Components.Make(G)

  let compute_dominators g s = 
    (* 
       compute the dominators for each node in g, with v being the start node -- 
       returns a function from nodes to a list of its dominators 
       Muchnick pg 182, Fig 7.14
    *)
    let change = ref true and
	dominatorTable = Hashtbl.create (G.nb_vertex g) and
	all_vertices = G.fold_vertex (fun v -> fun all -> VSet.add v all) g VSet.empty in
      begin
	G.iter_vertex (fun v -> Hashtbl.add dominatorTable v all_vertices) g;
	Hashtbl.replace dominatorTable s (VSet.add s VSet.empty);
	while (!change) do
	  (* repeat until no more changes *)
	  change := false;
	  G.iter_vertex 
	    (fun n ->
	       if not (n = s) then
		 begin
		   let t = 
		     G.fold_pred 
		       (fun p -> fun t ->
			  let pdoms = (Hashtbl.find dominatorTable p) in
			    VSet.inter pdoms t)
		       g n all_vertices in
		   let d = VSet.add n t in
		     if not (VSet.equal d (Hashtbl.find dominatorTable n)) then
		       begin
			 change := true;
			 Hashtbl.replace dominatorTable n d
		       end
		 end)
	    g
	done;
	fun v -> Hashtbl.find dominatorTable v
      end

  let compute_postdominators g s = 
    let mirror_g = Oper.mirror g in
      compute_dominators mirror_g s

end
