let () =
  let values = Rrbvec.of_list [ 1; 2; 3 ] in
  if Rrbvec.nth values 1 <> 2 then failwith "jsoo nth failed";
  if Rrbvec.nth_opt values 1 <> Some 2 then failwith "jsoo nth_opt failed";
  if Rrbvec.to_list (Rrbvec.push_back values 4) <> [ 1; 2; 3; 4 ] then
    failwith "jsoo push_back failed"
