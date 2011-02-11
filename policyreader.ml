let process_file_as_policy fn =
  try
    let file = open_in fn in
    let lexbuf = Lexing.from_channel file in
    let result = Obj.magic (Policyparser.main Policylexer.token lexbuf) in
      Placepolicy.policy := result;
      Printf.printf ("** POLICY **\n");
      Printf.printf ("-------------------------------------------------\n");
      Printf.printf "%s\n" (String.concat "\n" (List.map Placepolicy.policy_to_string result)); 
      Printf.printf ("-------------------------------------------------\n")
  with Policylexer.Eof ->
    exit 0

