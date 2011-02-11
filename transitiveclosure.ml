open Graph
open Simpgraph.SimpGraph

module type INT_GRAPH =
sig
  include Graph.Sig.I (* with type V.t = int and type V.label = int*)

  val v_to_string : V.t -> string
  val e_to_string : E.t -> string
  val edgelabel_to_string : E.label -> string
end

module TransitiveClosure = functor (G : INT_GRAPH) ->
struct
  let transitive_closure graph = 
    let n = (G.nb_vertex graph) in
      let superToNodeMap = Hashtbl.create n in
      let node = Hashtbl.find superToNodeMap in
      let r = ref (-1) in
	G.iter_vertex 
	  (fun v ->
	     r := (!r) + 1;
	     Hashtbl.replace superToNodeMap !r v
	  )
	  graph;
	let t = (Array.make_matrix n n false) in 
	  for i = 0 to n - 1 do
	    for j = 0 to n - 1 do 
	      if (G.mem_edge graph (node i) (node j)) then
		begin
		  t.(i).(j) <- true
		end
	    done
	  done;
	  for j = 0 to n - 1 do
	    for i = 0 to n - 1 do
	      if t.(i).(j) then
		begin
		  for k = 0 to n - 1 do
		    if (t.(j).(k)) then
		      begin
			t.(i).(k) <- true
		      end
		  done
		end
	    done
	  done;
	  let returnGraph = G.create ~size:(n + 1) () in
	    for i = 0 to n - 1 do
	      G.add_vertex returnGraph (node i)
	    done;
	    for i = 0 to n - 1 do
	      for j = 0 to n - 1 do
		if (t.(i).(j)) && (i != j) then
		  begin
		    G.add_edge returnGraph (node i) (node j);
		  end
	      done
            done;
	    returnGraph
end  
