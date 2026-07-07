let default_size = 50_000
let default_reads = 10_000
let default_updates = 5_000

type config = {
  size : int;
  reads : int;
  updates : int;
}

type measurement = {
  name : string;
  elapsed_ms : float;
}

type values = {
  rrbvec : int Rrbvec.t;
  batvect : int BatVect.t;
}

let current_measurements = ref []

let compare_measurements left right =
  match Float.compare left.elapsed_ms right.elapsed_ms with
  | 0 -> String.compare left.name right.name
  | order -> order

let print_group name measurements =
  let measurements = List.sort compare_measurements measurements in
  Printf.printf "%s:\n" name;
  List.iter
    (fun measurement ->
      Printf.printf "  %-46s %10.4f ms\n" measurement.name measurement.elapsed_ms)
    measurements;
  print_endline ""

let run_group name f =
  let previous_measurements = !current_measurements in
  current_measurements := [];
  match f () with
  | result ->
      let measurements = List.rev !current_measurements in
      current_measurements := previous_measurements;
      print_group name measurements;
      result
  | exception exn ->
      current_measurements := previous_measurements;
      raise exn

let parse_config () =
  let size = ref default_size in
  let reads = ref default_reads in
  let updates = ref default_updates in
  let spec =
    [
      ("--size", Arg.Set_int size, "Number of elements to build");
      ("--reads", Arg.Set_int reads, "Number of indexed reads");
      ("--updates", Arg.Set_int updates, "Number of random indexed writes");
    ]
  in
  Arg.parse spec
    (fun arg -> raise (Arg.Bad ("unexpected argument: " ^ arg)))
    "ivector-bench [--size N] [--reads N] [--updates N]";
  { size = !size; reads = !reads; updates = !updates }

let time name f =
  Gc.full_major ();
  let start = Sys.time () in
  let result = f () in
  let elapsed = Sys.time () -. start in
  current_measurements :=
    { name; elapsed_ms = elapsed *. 1000.0 } :: !current_measurements;
  result

let check name expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "%s: expected %d, got %d" name expected actual)

let make_indices count modulo_by =
  Array.init count (fun i -> (i * 1_103 + 12_345) mod modulo_by)

let range_sum start length = (start + start + length - 1) * length / 2

let sum_rrbvec values = Rrbvec.fold_left ( + ) 0 values
let sum_batvect values = BatVect.fold_left ( + ) 0 values

let check_rrbvec_invariants name values =
  try Rrbvec.invariants values
  with exn ->
    failwith
      (Printf.sprintf "%s: Rrbvec invariant failure: %s" name
         (Printexc.to_string exn))

let batvect_sub values start length = BatVect.sub values start length

let rrbvec_random_sum values indices =
  Array.fold_left (fun acc index -> acc + Rrbvec.get values index) 0 indices

let batvect_random_sum values indices =
  Array.fold_left (fun acc index -> acc + BatVect.get values index) 0 indices

let concat_nonempty combine = function
  | [] -> invalid_arg "expected at least one chunk"
  | first :: rest -> List.fold_left combine first rest

let chunk_bounds size chunks =
  let base = size / chunks in
  let remainder = size mod chunks in
  let rec loop index start acc =
    if index = chunks then List.rev acc
    else
      let length = base + if index < remainder then 1 else 0 in
      loop (index + 1) (start + length) ((start, length) :: acc)
  in
  loop 0 0 []

let update_rrbvec values indices =
  Array.fold_left
    (fun values (update_index, value_index) ->
      Rrbvec.set values value_index (-(update_index + 1)))
    values
    (Array.mapi (fun update_index value_index -> (update_index, value_index)) indices)

let update_batvect values indices =
  Array.fold_left
    (fun values (update_index, value_index) ->
      BatVect.set values value_index (-(update_index + 1)))
    values
    (Array.mapi (fun update_index value_index -> (update_index, value_index)) indices)

let expected_update_sum size indices =
  let values = Array.init size Fun.id in
  Array.iteri (fun i index -> values.(index) <- -(i + 1)) indices;
  Array.fold_left ( + ) 0 values

let bench_sequential_write config =
  let rrbvec =
    time "Rrbvec sequential write (push_back)" (fun () ->
        let rec loop i values =
          if i = config.size then values
          else loop (i + 1) (Rrbvec.push_back values i)
        in
        loop 0 Rrbvec.empty)
  in
  let batvect =
    time "BatVect sequential write (append)" (fun () ->
        let rec loop i values =
          if i = config.size then values
          else loop (i + 1) (BatVect.append i values)
        in
        loop 0 BatVect.empty)
  in
  let rrbvec_push_front =
    time "Rrbvec sequential write (push_front)" (fun () ->
        let rec loop i values =
          if i = config.size then values
          else loop (i + 1) (Rrbvec.push_front values i)
        in
        loop 0 Rrbvec.empty)
  in
  let batvect_push_front =
    time "BatVect sequential write (push_front)" (fun () ->
        let rec loop i values =
          if i = config.size then values
          else loop (i + 1) (BatVect.prepend i values)
        in
        loop 0 BatVect.empty)
  in
  check_rrbvec_invariants "Rrbvec sequential write (push_back)" rrbvec;
  check_rrbvec_invariants "Rrbvec sequential write (push_front)"
    rrbvec_push_front;
  let expected_sum = range_sum 0 config.size in
  check "Rrbvec sequential write length" config.size (Rrbvec.length rrbvec);
  check "BatVect sequential write length" config.size (BatVect.length batvect);
  check "Rrbvec sequential write push_front length" config.size
    (Rrbvec.length rrbvec_push_front);
  check "BatVect sequential write push_front length" config.size
    (BatVect.length batvect_push_front);
  check "Rrbvec sequential write sum" expected_sum (sum_rrbvec rrbvec);
  check "BatVect sequential write sum" expected_sum (sum_batvect batvect);
  check "Rrbvec sequential write push_front sum" expected_sum
    (sum_rrbvec rrbvec_push_front);
  check "BatVect sequential write push_front sum" expected_sum
    (sum_batvect batvect_push_front);
  { rrbvec; batvect }

let bench_sequential_read values =
  let expected = sum_rrbvec values.rrbvec in
  check "Rrbvec sequential read" expected
    (time "Rrbvec sequential read (fold_left)" (fun () ->
         Rrbvec.fold_left ( + ) 0 values.rrbvec));
  check "Rrbvec reverse sequential read" expected
    (time "Rrbvec sequential read (fold_right)" (fun () ->
         Rrbvec.fold_right ( + ) values.rrbvec 0));
  check "BatVect sequential read" expected
    (time "BatVect sequential read (fold_left)" (fun () ->
         BatVect.fold_left ( + ) 0 values.batvect));
  check "BatVect reverse sequential read" expected
    (time "BatVect sequential read (fold_right)" (fun () ->
         BatVect.fold_right ( + ) values.batvect 0))

let bench_random_read config values =
  let indices = make_indices config.reads config.size in
  let expected = Array.fold_left ( + ) 0 indices in
  check "Rrbvec random read" expected
    (time "Rrbvec random read" (fun () ->
         rrbvec_random_sum values.rrbvec indices));
  check "BatVect random read" expected
    (time "BatVect random read" (fun () ->
         batvect_random_sum values.batvect indices))

let bench_random_write config values =
  let indices = make_indices config.updates config.size in
  let expected = expected_update_sum config.size indices in
  let rrbvec_updated =
    time "Rrbvec random write (set)" (fun () ->
        update_rrbvec values.rrbvec indices)
  in
  check_rrbvec_invariants "Rrbvec random write (set)" rrbvec_updated;
  check "Rrbvec random write (set)" expected (sum_rrbvec rrbvec_updated);
  let batvect_updated =
    time "BatVect random write (set)" (fun () ->
        update_batvect values.batvect indices)
  in
  check "BatVect random write (set)" expected (sum_batvect batvect_updated)

let repeated_rrbvec_subvec steps values =
  let rec loop steps values =
    if steps = 0 then values
    else
      let length = Rrbvec.length values in
      loop (steps - 1) (Rrbvec.subvec values 1 (length - 1))
  in
  loop steps values

let repeated_batvect_subvec steps values =
  let rec loop steps values =
    if steps = 0 then values
    else
      let length = BatVect.length values in
      loop (steps - 1) (batvect_sub values 1 (length - 2))
  in
  loop steps values

let bench_subvec_concat config values =
  let subvec_steps = min 8 ((config.size - 1) / 2) in
  let final_length = config.size - (2 * subvec_steps) in
  let expected_subvec_sum = range_sum subvec_steps final_length in
  let rrbvec_subvec =
    time "Rrbvec repeated subvec" (fun () ->
        repeated_rrbvec_subvec subvec_steps values.rrbvec)
  in
  check_rrbvec_invariants "Rrbvec repeated subvec" rrbvec_subvec;
  check "Rrbvec repeated subvec length" final_length
    (Rrbvec.length rrbvec_subvec);
  check "Rrbvec repeated subvec sum" expected_subvec_sum
    (sum_rrbvec rrbvec_subvec);
  let batvect_subvec =
    time "BatVect repeated subvec" (fun () ->
        repeated_batvect_subvec subvec_steps values.batvect)
  in
  check "BatVect repeated subvec length" final_length
    (BatVect.length batvect_subvec);
  check "BatVect repeated subvec sum" expected_subvec_sum
    (sum_batvect batvect_subvec);
  let chunks = min 8 config.size in
  let bounds = chunk_bounds config.size chunks in
  let expected_concat_sum = range_sum 0 config.size in
  let rrbvec_concat =
    time "Rrbvec repeated concat" (fun () ->
        bounds
        |> List.map (fun (start, length) ->
               Rrbvec.subvec values.rrbvec start (start + length))
        |> concat_nonempty Rrbvec.concat)
  in
  check_rrbvec_invariants "Rrbvec repeated concat" rrbvec_concat;
  check "Rrbvec repeated concat length" config.size (Rrbvec.length rrbvec_concat);
  check "Rrbvec repeated concat sum" expected_concat_sum
    (sum_rrbvec rrbvec_concat);
  let batvect_concat =
    time "BatVect repeated concat" (fun () ->
        bounds
        |> List.map (fun (start, length) ->
               batvect_sub values.batvect start length)
        |> concat_nonempty BatVect.concat)
  in
  check "BatVect repeated concat length" config.size
    (BatVect.length batvect_concat);
  check "BatVect repeated concat sum" expected_concat_sum
    (sum_batvect batvect_concat)

let bench_push_pop config =
  let rrbvec_after_push_pop =
    time "Rrbvec push then pop" (fun () ->
        let rec push_loop i values =
          if i = config.size then values
          else push_loop (i + 1) (Rrbvec.push_back values i)
        in
        let rec pop_loop values =
          if Rrbvec.is_empty values then values
          else pop_loop (snd (Rrbvec.pop_back values))
        in
        pop_loop (push_loop 0 Rrbvec.empty))
  in
  check_rrbvec_invariants "Rrbvec push then pop" rrbvec_after_push_pop;
  ignore
    (time "BatVect append then pop" (fun () ->
         let rec push_loop i values =
           if i = config.size then values
           else push_loop (i + 1) (BatVect.append i values)
         in
         let rec pop_loop values =
           if BatVect.is_empty values then values
           else pop_loop (snd (BatVect.pop values))
         in
         pop_loop (push_loop 0 BatVect.empty)))

let () =
  let config = parse_config () in
  if config.size <= 0 || config.reads < 0 || config.updates < 0 then
    invalid_arg "benchmark sizes must be positive";
  Printf.printf "size=%d reads=%d updates=%d\n\n" config.size config.reads
    config.updates;
  let values =
    run_group "Sequential write" (fun () -> bench_sequential_write config)
  in
  run_group "Sequential read" (fun () -> bench_sequential_read values);
  run_group "Random read" (fun () -> bench_random_read config values);
  run_group "Random write" (fun () -> bench_random_write config values);
  run_group "Subvec and concat" (fun () -> bench_subvec_concat config values);
  run_group "Push/pop" (fun () -> bench_push_pop config)
