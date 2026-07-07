let () =
  let values = Rrbvec.of_list [ 1; 2; 3 ] in
  if Rrbvec.get values 1 <> 2 then failwith "native get failed";
  if Rrbvec.to_list (Rrbvec.push_back values 4) <> [ 1; 2; 3; 4 ] then
    failwith "native push_back failed"
