let () =
  let values = Rrbvec.of_list [ 1; 2; 3 ] in
  if Rrbvec.nth values 1 <> 2 then Js.Exn.raiseError "melange nth failed";
  if Rrbvec.nth_opt values 1 <> Some 2 then
    Js.Exn.raiseError "melange nth_opt failed";
  if Rrbvec.to_list (Rrbvec.push_back values 4) <> [ 1; 2; 3; 4 ] then
    Js.Exn.raiseError "melange push_back failed";
  let rec double remaining values =
    if remaining = 0 then values
    else double (remaining - 1) (Rrbvec.concat values values)
  in
  let half = double (Sys.int_size - 2) (Rrbvec.singleton 7) in
  match Rrbvec.concat half half with
  | exception Invalid_argument _ -> ()
  | _ -> Js.Exn.raiseError "melange count overflow check failed"
