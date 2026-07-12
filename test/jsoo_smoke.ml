let () =
  let values = Rrbvec.of_list [ 1; 2; 3 ] in
  if Rrbvec.nth values 1 <> 2 then failwith "jsoo nth failed";
  if Rrbvec.nth_opt values 1 <> Some 2 then failwith "jsoo nth_opt failed";
  if Rrbvec.to_list (Rrbvec.push_back values 4) <> [ 1; 2; 3; 4 ] then
    failwith "jsoo push_back failed";
  let rec double remaining values =
    if remaining = 0 then values
    else double (remaining - 1) (Rrbvec.concat values values)
  in
  let half = double (Sys.int_size - 2) (Rrbvec.singleton 7) in
  match Rrbvec.concat half half with
  | exception Invalid_argument _ -> ()
  | _ -> failwith "jsoo count overflow check failed"
