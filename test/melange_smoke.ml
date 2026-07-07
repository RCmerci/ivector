let () =
  let values = Rrbvec.of_list [ 1; 2; 3 ] in
  if Rrbvec.get values 1 <> 2 then Js.Exn.raiseError "melange get failed";
  if Rrbvec.to_list (Rrbvec.push_back values 4) <> [ 1; 2; 3; 4 ] then
    Js.Exn.raiseError "melange push_back failed"
