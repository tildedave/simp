let verbose = ref false
let output_dot = ref false
let fca = ref false
let debug = ref false
let cluster = ref true
let lgf = ref false

let procedure_list : (string * int) list ref = ref []
let pc_decl = ref false
let no_multiple_sources = ref false
let compact_graph = ref false
let aggressive_cluster = ref false

let timeThunk th timeFunc = 
  timeFunc true 0.0;
  let startTime = Unix.gettimeofday () in
  let rv = th () in
  let stopTime = Unix.gettimeofday ()
  in 
    timeFunc false (stopTime -. startTime);
    flush stdout;
    rv

let print_dashed_line () = 
  Printf.printf ("-------------------------------------------------\n")

module SimpTimer =
struct
  let currentHashNumber = ref 0
  let hash_time = Hashtbl.create 10

  let record_time ?silent:(silent=false) s start t =
    if (start && !verbose && not silent) then
      begin
	Printf.printf ("\tstarting %s\n") s; flush stdout
      end
    else
      begin
	if (Hashtbl.mem hash_time s) then
	  let (current_index,old_t) = Hashtbl.find hash_time s in
	    Hashtbl.replace hash_time s (current_index,t +. old_t)
	else
	  begin
	  let index = !currentHashNumber in 
	    currentHashNumber := (!currentHashNumber) + 1;
	    Hashtbl.add hash_time s (index,t)
	  end;
	if (!verbose && not silent) then
	  begin
	    Printf.printf ("\tfinished %s (time: %.2fs)\n") s t; flush stdout
	  end
      end

  let print_times () = 
    let print_time s v = Printf.printf ("%-35s: %.3f (s)\n") s v in
    let sorted_list = 
      List.sort 
	(fun p1 -> fun p2 -> compare (fst p1) (fst p2)) 
	(Hashtbl.fold (fun s -> fun (t,v) -> fun l -> (t,(s,v)) :: l) hash_time [])
    in
      print_dashed_line ();
      Printf.printf ("** TIMES **\n");
      print_dashed_line ();
      List.iter (fun (i,(s,t)) -> print_time s t) sorted_list

end

exception Interrupt of string
