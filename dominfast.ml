open Graph
open Simpgraph.SimpGraph

module type INT_GRAPH =
sig
  include Graph.Sig.I (*with type V.t = int*)

  val v_to_string : V.t -> string
  val e_to_string : E.t -> string
  val edgelabel_to_string : E.label -> string
end

module Dominators = functor (G : INT_GRAPH) ->
struct

  module VSet = Set.Make(struct type t = G.V.t let compare = compare end)
  module Oper = Oper.I(G)
  module Components = Components.Make(G)

  let compute_immediate_dominators g s junk = 
    (* 
       compute the dominators for each node in g, with v being the start node -- 
       returns a function from nodes to a list of its dominators 
       Muchnick pg 186, Fig 7.16 - Fig 7.18
    *)
    let num_nodes = G.nb_vertex g in
    let labelMap = Hashtbl.create num_nodes and
	parentMap = Hashtbl.create num_nodes and
	ancestorMap = Hashtbl.create num_nodes and
	childMap = Hashtbl.create num_nodes in
    let ndfsMap = Hashtbl.create num_nodes in
    let sdnoMap = Hashtbl.create num_nodes and 
	sizeMap = Hashtbl.create num_nodes in
    let	bucketMap = Hashtbl.create num_nodes in
      (* idomMap: what we return *)
    let idomMap = Hashtbl.create num_nodes in
    let bucket = Hashtbl.find bucketMap and
	parent = Hashtbl.find parentMap and 
	sdno = Hashtbl.find sdnoMap and
	ndfs = Hashtbl.find ndfsMap and
	idom = Hashtbl.find idomMap and
	label = Hashtbl.find labelMap and
	ancestor = Hashtbl.find ancestorMap and
	child = Hashtbl.find childMap and
	size = Hashtbl.find sizeMap
    in
    let n0 = G.V.create junk in
    let n = ref 0 in
    let rec depth_first_search_dom v = 
      n := (!n) + 1;
      Hashtbl.add sdnoMap v (!n);
      Hashtbl.add ndfsMap (!n) v;
      Hashtbl.add labelMap v v;
      Hashtbl.add ancestorMap v n0;
      Hashtbl.add childMap v n0;
      Hashtbl.add sizeMap v 1;
      (*Printf.printf ("visiting %s\n") (G.v_to_string v);*)
      G.iter_succ 
	(fun w ->
	   if (sdno w) = 0 then
	     begin
	       Hashtbl.replace parentMap w v;
	       depth_first_search_dom w
	     end
	   (*else
	     Printf.printf("don't need to visit %s\n") (G.v_to_string v)*)
	)
	g v in
    let rec compress v = 
      if (ancestor (ancestor v)) != n0 then
	begin
	  compress (ancestor v);
	  if (sdno (label (ancestor v))) < sdno (label v) then
	    Hashtbl.replace labelMap v (label (ancestor v));
	  Hashtbl.replace ancestorMap v (ancestor (ancestor v))
	end
    in
    let eval v = 
      (*Printf.printf ("beginning eval for node %s -- %b %b %b %d\n") (G.v_to_string v) (Hashtbl.mem ancestorMap v) (Hashtbl.mem childMap v) (Hashtbl.mem sdnoMap v) (sdno v);*)
      let ret = if (ancestor v) = n0 then
	(label v)
      else
	begin
	  compress v;
	  if (sdno (label (ancestor v))) >= (sdno (label v)) then
	    (label v)
	  else 
	    (label (ancestor v))
	end in
	(*Printf.printf ("finished eval\n");*)
	ret
    in
    let link v w = 
      let s = ref w 
      in
	while (sdno (label w)) < (sdno (label (child (!s)))) do
	  if (size (!s)) + (size (child (child (!s)))) >= 2 * (size (child (!s))) then
	    begin
	      Hashtbl.replace ancestorMap (child (!s)) (!s);
	      Hashtbl.replace childMap (!s) (child (child (!s)))
	    end
	  else
	    begin
	      Hashtbl.replace sizeMap (child (!s)) (size (!s));
	      Hashtbl.replace ancestorMap (!s) (child !s);
	      s := (ancestor (!s))
	    end
	done;
	Hashtbl.replace labelMap (!s) (label w);
	Hashtbl.replace sizeMap v ((size v) + (size w));
	if (size v) < 2 * (size w) then
	  (let tmp = (!s) in
	    s := (child v);
	    Hashtbl.replace childMap v tmp);
	while (!s) != n0 do
	  Hashtbl.replace ancestorMap (!s) v;
	  s := (child (!s))
	done
    in
      begin
	G.iter_vertex
	  (fun v -> 
	     Hashtbl.replace bucketMap v VSet.empty;
	     Hashtbl.replace sdnoMap v 0;
	     Hashtbl.replace idomMap v n0
	  )
	  g;
	Hashtbl.replace sizeMap n0 0;
	Hashtbl.replace sdnoMap n0 0;
	Hashtbl.replace ancestorMap n0 n0;
	Hashtbl.replace labelMap n0 n0;
	depth_first_search_dom s;
	for i = (!n) downto 2 do
	  let w = ndfs i in
	    G.iter_pred
	      (fun v -> 
		 if (sdno v) != 0 then
		   let u = eval v in
		     if (sdno u) < (sdno w) then
		       begin
			 (*Printf.printf ("setting sdno(%s) = %d\n") (G.v_to_string w) (sdno u);*)
			 Hashtbl.replace sdnoMap w (sdno u)
		       end
	      )
	      g w;
	    let ndfsSdno_w = ndfs (sdno w) in	      
	    let current_bucket = bucket (ndfs (sdno w)) in 
	      Hashtbl.replace bucketMap ndfsSdno_w (VSet.add w current_bucket);
	      link (Hashtbl.find parentMap w) w;
	      (* compute immediate dominators for nodes in the bucket *)
	      while not (VSet.is_empty (bucket (parent w))) do 
		let v = VSet.choose (bucket (parent w)) in
		  Hashtbl.replace 
		    bucketMap
		    (parent w)
		    (VSet.remove v (bucket (parent w)));
		  let u = eval v in
		    if (sdno u) < (sdno v) then
		      begin
			Hashtbl.replace idomMap v u;
		      end
		    else
		      begin
			Hashtbl.replace idomMap v (parent w);
		      end
	      done
	done;
	for i = 2 to (!n) do
	  let w = ndfs i in
	    if (idom w) != ndfs (sdno w) then
	      Hashtbl.replace idomMap w (idom (idom w));
	done;
	idomMap
      end

  let compute_dominators g s j = compute_immediate_dominators g s j
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

module DominfastTester = Dominators(TestGraph)

let testGraph = TestGraph.create ()

let _ =
  begin
    TestGraph.add_vertex testGraph 0;
    TestGraph.add_vertex testGraph 1;
    TestGraph.add_vertex testGraph 2;
    TestGraph.add_vertex testGraph 3;
    TestGraph.add_vertex testGraph 4;
    TestGraph.add_vertex testGraph 5;
    TestGraph.add_vertex testGraph 6;
    TestGraph.add_vertex testGraph 7;

    TestGraph.add_edge_e testGraph (0,1,1);
    TestGraph.add_edge_e testGraph (1,1,2);
    TestGraph.add_edge_e testGraph (1,1,3);
    TestGraph.add_edge_e testGraph (3,1,4);
    TestGraph.add_edge_e testGraph (4,1,6);
    TestGraph.add_edge_e testGraph (6,1,4);
    TestGraph.add_edge_e testGraph (4,1,5);
    TestGraph.add_edge_e testGraph (5,1,7);
    TestGraph.add_edge_e testGraph (2,1,7);

    DominfastTester.compute_dominators testGraph 0 (-1)
  end
