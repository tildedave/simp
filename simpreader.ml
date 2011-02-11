open Simpdecl
open Simpconsreader
open Simputil

let read_from_confile = ref false

let process_file_as_program fn =
  try
    let file = open_in fn in
    let lexbuf = Lexing.from_channel file in
    let result = Simpparser.main Simplexer.token lexbuf in
    let _ = timeThunk
      (fun _ ->
	 Printf.printf ("** PROGRAM **\n");
	 Printf.printf ("-------------------------------------------------\n");
	 Printf.printf "%s\n" (Simp.command_to_string result); 
	 print_newline(); 
	 (*
	   Printf.printf ("-------------------------------------------------\n");
	   Printf.printf ("** CONSTRAINTS **\n");
	   List.iter (fun con -> Printf.printf ("  %s\n") (Simp.cons_to_string con)) (Simp.command_to_constraints result);
	   print_newline(); 
	 *)
	 Printf.printf ("-------------------------------------------------\n");
	 Printf.printf("** SUGGESTED DECLASSIFIER EQUIVALENCE CLASSES **\n");
	 propose_declassifiers result fn Simp.defaultLattice)
      (SimpTimer.record_time "total")
    in
      if (!Simputil.verbose) then 
	SimpTimer.print_times ();
      print_dashed_line ()
  with Simplexer.Eof ->
    exit 0

let process_file_as_xml_file fn =
  Printf.printf ("** CONSTRAINT FILE %s **\n") fn;
  print_dashed_line ();
  if (!Simputil.verbose) then Printf.printf ("reading constraint file...\n");
  flush stdout;
  let _ = timeThunk 
    (fun _ ->
       let (cons,lattice,procedures) = timeThunk (fun _ -> XmlConstraintReader.xml_file_to_constraint_set fn) (SimpTimer.record_time "read constraints") in
	 Printf.printf ("# constraints: %d\n") (List.length cons);
	 flush stdout;
	 Simputil.procedure_list := procedures;
	 let congraph = constraint_set_to_flowgraph cons fn lattice in 
	   print_dashed_line ();
	   Printf.printf ("** SUGGESTED DECLASSIFIER EQUIVALENCE CLASSES **\n");
	   flush stdout;
	   propose_declassifiers_for_flowgraph congraph fn lattice)
    (SimpTimer.record_time "total")
  in
    if (!Simputil.verbose) then 
      SimpTimer.print_times ();
    print_dashed_line ();
    flush stdout

let _ = 
  Arg.parse 
    [ 
      ("-c", 
       Arg.Unit (fun () -> read_from_confile := true), 
       "read from Constraint File");
      ("-v",
       Arg.Unit (fun () -> Simputil.verbose := true), 
       "verbose");
      ("-dot",
       Arg.Unit (fun () -> Simputil.output_dot := true),
       "output as DOT file and convert to PNG");
      ("-declout",
       Arg.Unit (fun () -> Simp.output_declassifiers := true),
       "output declassifiers to xml file");
      ("-fca",
       Arg.Unit (fun () -> Simputil.fca := true),
       "use formal concept analysis to cluster declassifiers");
      ("-nocluster",
       Arg.Unit (fun () -> Simputil.cluster := false),
       "turn off dominator-based clustering");
      ("-pp",
       Arg.String (Policyreader.process_file_as_policy),
       "placement policy file");
      ("-pcdecl",
       Arg.Unit (fun () -> Simputil.pc_decl := true),
       "allow PC-based declassifications (for SSO computation)");
      ("-nomultiplesources",
       Arg.Unit (fun () -> Simputil.no_multiple_sources := true),
       "don't mediate expressions to a label that they do not dominate (for authorization queries)");
      ("-compact",
       Arg.Unit (fun () -> Simputil.compact_graph := true),
       "compact graph based on procedures");
      ("-aggressive",
       Arg.Unit (fun () -> Simputil.aggressive_cluster := true),
       "aggressively cluster graph");
      ("-debug",
       Arg.Unit (fun () -> Simputil.debug := true),
       "turn on debug output");
      ("-lgf",
       Arg.Unit (fun () -> Simputil.lgf := true),
       "output graph in LGF (Lemon Graph Format)");
    ]
    (fun fn -> 
       if ((!read_from_confile) = false) then
	 process_file_as_program fn
       else
	 process_file_as_xml_file fn)
    "simpreader usage"
