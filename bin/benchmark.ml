let default_size = 50_000
let default_reads = 10_000
let default_updates = 5_000

type config = {
  size : int;
  reads : int;
  updates : int;
}

let parse_config () =
  let size = ref default_size in
  let reads = ref default_reads in
  let updates = ref default_updates in
  let spec =
    [
      ("--size", Arg.Set_int size, "Number of elements to build");
      ("--reads", Arg.Set_int reads, "Number of indexed reads");
      ("--updates", Arg.Set_int updates, "Number of indexed updates");
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
  Printf.printf "%-34s %10.4f ms\n%!" name (elapsed *. 1000.0);
  result

let make_indices count modulo_by =
  Array.init count (fun i -> (i * 1_103 + 12_345) mod modulo_by)

let list_set index value values =
  let rec loop i = function
    | [] -> invalid_arg "index out of bounds"
    | _ :: xs when i = index -> value :: xs
    | x :: xs -> x :: loop (i + 1) xs
  in
  loop 0 values

let list_random_sum values indices =
  Array.fold_left (fun acc index -> acc + List.nth values index) 0 indices

let array_random_sum values indices =
  Array.fold_left (fun acc index -> acc + values.(index)) 0 indices

let dynarray_random_sum values indices =
  Array.fold_left (fun acc index -> acc + Dynarray.get values index) 0 indices

let ivector_random_sum values indices =
  Array.fold_left (fun acc index -> acc + Ivector.get values index) 0 indices

let rec list_drop count values =
  if count = 0 then values
  else
    match values with
    | [] -> []
    | _ :: rest -> list_drop (count - 1) rest

let list_take count values =
  let rec loop count values acc =
    if count = 0 then List.rev acc
    else
      match values with
      | [] -> invalid_arg "not enough values"
      | value :: rest -> loop (count - 1) rest (value :: acc)
  in
  loop count values []

let list_sub values start length = list_drop start values |> list_take length

let dynarray_sub values start length =
  Dynarray.init length (fun i -> Dynarray.get values (start + i))

let concat_nonempty combine = function
  | [] -> invalid_arg "expected at least one chunk"
  | first :: rest -> List.fold_left combine first rest

let sum_array values = Array.fold_left ( + ) 0 values

let sum_dynarray values =
  let sum = ref 0 in
  for i = 0 to Dynarray.length values - 1 do
    sum := !sum + Dynarray.get values i
  done;
  !sum

let sum_ivector values = Ivector.fold_left ( + ) 0 values

let update_array values indices =
  let values = Array.copy values in
  Array.iteri (fun i index -> values.(index) <- -(i + 1)) indices;
  values

let update_dynarray values indices =
  let values = Dynarray.copy values in
  Array.iteri (fun i index -> Dynarray.set values index (-(i + 1))) indices;
  values

let update_list values indices =
  let values = ref values in
  Array.iteri (fun i index -> values := list_set index (-(i + 1)) !values) indices;
  !values

let update_ivector values indices =
  let values = ref values in
  Array.iteri (fun i index -> values := Ivector.set !values index (-(i + 1))) indices;
  !values

let bench_build config =
  let list_values =
    time "list build (cons + rev)" (fun () ->
        let rec loop i acc =
          if i = config.size then List.rev acc else loop (i + 1) (i :: acc)
        in
        loop 0 [])
  in
  let array_values =
    time "array build (init)" (fun () -> Array.init config.size Fun.id)
  in
  let dynarray_values =
    time "Dynarray build (add_last)" (fun () ->
        let values = Dynarray.create () in
        for i = 0 to config.size - 1 do
          Dynarray.add_last values i
        done;
        values)
  in
  let ivector_values =
    time "Ivector build (push)" (fun () ->
        let rec loop i values =
          if i = config.size then values else loop (i + 1) (Ivector.push values i)
        in
        loop 0 Ivector.empty)
  in
  (list_values, array_values, dynarray_values, ivector_values)

let bench_sequential_read (list_values, array_values, dynarray_values, ivector_values) =
  let check name expected actual =
    if expected <> actual then failwith (name ^ ": unexpected sum")
  in
  let expected = List.fold_left ( + ) 0 list_values in
  check "array sequential read" expected
    (time "array sequential read" (fun () ->
         let sum = ref 0 in
         for i = 0 to Array.length array_values - 1 do
           sum := !sum + array_values.(i)
         done;
         !sum));
  check "Dynarray sequential read" expected
    (time "Dynarray sequential read" (fun () ->
         let sum = ref 0 in
         for i = 0 to Dynarray.length dynarray_values - 1 do
           sum := !sum + Dynarray.get dynarray_values i
         done;
         !sum));
  check "Ivector sequential read" expected
    (time "Ivector sequential read (fold_left)" (fun () ->
         Ivector.fold_left ( + ) 0 ivector_values));
  check "list sequential read" expected
    (time "list sequential read" (fun () -> List.fold_left ( + ) 0 list_values))

let bench_random_read config (list_values, array_values, dynarray_values, ivector_values) =
  let indices = make_indices config.reads config.size in
  let expected = array_random_sum array_values indices in
  let check name actual =
    if expected <> actual then failwith (name ^ ": unexpected sum")
  in
  check "array random read"
    (time "array random read" (fun () -> array_random_sum array_values indices));
  check "Dynarray random read"
    (time "Dynarray random read" (fun () -> dynarray_random_sum dynarray_values indices));
  check "Ivector random read"
    (time "Ivector random read" (fun () -> ivector_random_sum ivector_values indices));
  check "list random read"
    (time "list random read (List.nth)" (fun () ->
         list_random_sum list_values indices))

let bench_updates config (list_values, array_values, dynarray_values, ivector_values) =
  let indices = make_indices config.updates config.size in
  ignore
    (time "array mutable set" (fun () ->
         let values = Array.copy array_values in
         Array.iteri (fun i index -> values.(index) <- -i) indices;
         values));
  ignore
    (time "Dynarray mutable set" (fun () ->
         let values = Dynarray.copy dynarray_values in
         Array.iteri (fun i index -> Dynarray.set values index (-i)) indices;
         values));
  ignore
    (time "Ivector persistent set" (fun () ->
         Array.fold_left
           (fun values index -> Ivector.set values index (-index))
           ivector_values indices));
  ignore
    (time "list persistent set" (fun () ->
         Array.fold_left
           (fun values index -> list_set index (-index) values)
           list_values indices))

let bench_subvec_concat config (list_values, array_values, dynarray_values, ivector_values) =
  let check name expected actual =
    if expected <> actual then failwith (name ^ ": unexpected value")
  in
  let start = config.size / 4 in
  let slice_length = config.size / 2 in
  let stop = start + slice_length in
  let expected_slice_sum =
    (start + stop - 1) * slice_length / 2
  in
  let list_slice =
    time "list subvec (drop + take)" (fun () ->
        list_sub list_values start slice_length)
  in
  check "list subvec length" slice_length (List.length list_slice);
  check "list subvec sum" expected_slice_sum (List.fold_left ( + ) 0 list_slice);
  let array_slice =
    time "array subvec (Array.sub)" (fun () ->
        Array.sub array_values start slice_length)
  in
  check "array subvec length" slice_length (Array.length array_slice);
  check "array subvec sum" expected_slice_sum (sum_array array_slice);
  let dynarray_slice =
    time "Dynarray subvec (init/get)" (fun () ->
        dynarray_sub dynarray_values start slice_length)
  in
  check "Dynarray subvec length" slice_length (Dynarray.length dynarray_slice);
  check "Dynarray subvec sum" expected_slice_sum (sum_dynarray dynarray_slice);
  let ivector_slice =
    time "Ivector subvec" (fun () -> Ivector.subvec ivector_values start stop)
  in
  check "Ivector subvec length" slice_length (Ivector.length ivector_slice);
  check "Ivector subvec sum" expected_slice_sum (sum_ivector ivector_slice);
  let half = config.size / 2 in
  let list_left = list_sub list_values 0 half in
  let list_right = list_sub list_values half (config.size - half) in
  let array_left = Array.sub array_values 0 half in
  let array_right = Array.sub array_values half (config.size - half) in
  let dynarray_left = dynarray_sub dynarray_values 0 half in
  let dynarray_right = dynarray_sub dynarray_values half (config.size - half) in
  let ivector_left = Ivector.subvec ivector_values 0 half in
  let ivector_right = Ivector.subvec ivector_values half config.size in
  let expected_concat_sum = config.size * (config.size - 1) / 2 in
  let list_concat =
    time "list concat (@)" (fun () -> list_left @ list_right)
  in
  check "list concat length" config.size (List.length list_concat);
  check "list concat sum" expected_concat_sum (List.fold_left ( + ) 0 list_concat);
  let array_concat =
    time "array concat (append)" (fun () -> Array.append array_left array_right)
  in
  check "array concat length" config.size (Array.length array_concat);
  check "array concat sum" expected_concat_sum (sum_array array_concat);
  let dynarray_concat =
    time "Dynarray concat (copy+append)" (fun () ->
        let values = Dynarray.copy dynarray_left in
        Dynarray.append values dynarray_right;
        values)
  in
  check "Dynarray concat length" config.size (Dynarray.length dynarray_concat);
  check "Dynarray concat sum" expected_concat_sum (sum_dynarray dynarray_concat);
  let ivector_concat =
    time "Ivector concat" (fun () -> Ivector.concat ivector_left ivector_right)
  in
  check "Ivector concat length" config.size (Ivector.length ivector_concat);
  check "Ivector concat sum" expected_concat_sum (sum_ivector ivector_concat)

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

let bench_read_write_after label config length
    (list_values, array_values, dynarray_values, ivector_values) =
  let check name expected actual =
    if expected <> actual then failwith (name ^ ": unexpected value")
  in
  let expected_sequential_sum = sum_array array_values in
  check ("array " ^ label ^ " sequential read") expected_sequential_sum
    (time ("array " ^ label ^ " sequential read") (fun () ->
         sum_array array_values));
  check ("Dynarray " ^ label ^ " sequential read") expected_sequential_sum
    (time ("Dynarray " ^ label ^ " sequential read") (fun () ->
         sum_dynarray dynarray_values));
  check ("Ivector " ^ label ^ " sequential read") expected_sequential_sum
    (time ("Ivector " ^ label ^ " sequential read") (fun () ->
         sum_ivector ivector_values));
  check ("list " ^ label ^ " sequential read") expected_sequential_sum
    (time ("list " ^ label ^ " sequential read") (fun () ->
         List.fold_left ( + ) 0 list_values));
  let ivector_list =
    time ("Ivector " ^ label ^ " to_list") (fun () ->
        Ivector.to_list ivector_values)
  in
  check ("Ivector " ^ label ^ " to_list length") length (List.length ivector_list);
  check ("Ivector " ^ label ^ " to_list sum") expected_sequential_sum
    (List.fold_left ( + ) 0 ivector_list);
  let read_indices = make_indices config.reads length in
  let expected_read_sum = array_random_sum array_values read_indices in
  check ("array " ^ label ^ " random read") expected_read_sum
    (time ("array " ^ label ^ " random read") (fun () ->
         array_random_sum array_values read_indices));
  check ("Dynarray " ^ label ^ " random read") expected_read_sum
    (time ("Dynarray " ^ label ^ " random read") (fun () ->
         dynarray_random_sum dynarray_values read_indices));
  check ("Ivector " ^ label ^ " random read") expected_read_sum
    (time ("Ivector " ^ label ^ " random read") (fun () ->
         ivector_random_sum ivector_values read_indices));
  check ("list " ^ label ^ " random read") expected_read_sum
    (time ("list " ^ label ^ " random read") (fun () ->
         list_random_sum list_values read_indices));
  let update_indices = make_indices config.updates length in
  let array_updated =
    time ("array " ^ label ^ " set") (fun () ->
        update_array array_values update_indices)
  in
  let expected_update_sum = sum_array array_updated in
  let dynarray_updated =
    time ("Dynarray " ^ label ^ " set") (fun () ->
        update_dynarray dynarray_values update_indices)
  in
  check ("Dynarray " ^ label ^ " set") expected_update_sum
    (sum_dynarray dynarray_updated);
  let ivector_updated =
    time ("Ivector " ^ label ^ " set") (fun () ->
        update_ivector ivector_values update_indices)
  in
  check ("Ivector " ^ label ^ " set") expected_update_sum
    (sum_ivector ivector_updated);
  let list_updated =
    time ("list " ^ label ^ " set") (fun () ->
        update_list list_values update_indices)
  in
  check ("list " ^ label ^ " set") expected_update_sum
    (List.fold_left ( + ) 0 list_updated)

let bench_repeated_concat_subvec config
    (list_values, array_values, dynarray_values, ivector_values) =
  let check name expected actual =
    if expected <> actual then failwith (name ^ ": unexpected value")
  in
  let chunks = min 8 config.size in
  let bounds = chunk_bounds config.size chunks in
  let list_concat =
    time "list repeated concat build" (fun () ->
        bounds
        |> List.map (fun (start, length) -> list_sub list_values start length)
        |> concat_nonempty ( @ ))
  in
  let array_concat =
    time "array repeated concat build" (fun () ->
        bounds
        |> List.map (fun (start, length) -> Array.sub array_values start length)
        |> concat_nonempty Array.append)
  in
  let dynarray_concat =
    time "Dynarray repeated concat build" (fun () ->
        bounds
        |> List.map (fun (start, length) -> dynarray_sub dynarray_values start length)
        |> concat_nonempty (fun left right ->
               let values = Dynarray.copy left in
               Dynarray.append values right;
               values))
  in
  let ivector_concat =
    time "Ivector repeated concat build" (fun () ->
        bounds
        |> List.map (fun (start, length) ->
               Ivector.subvec ivector_values start (start + length))
        |> concat_nonempty Ivector.concat)
  in
  check "list repeated concat length" config.size (List.length list_concat);
  check "array repeated concat length" config.size (Array.length array_concat);
  check "Dynarray repeated concat length" config.size
    (Dynarray.length dynarray_concat);
  check "Ivector repeated concat length" config.size
    (Ivector.length ivector_concat);
  bench_read_write_after "repeated concat" config config.size
    (list_concat, array_concat, dynarray_concat, ivector_concat);
  print_endline "";
  let subvec_steps = min 8 ((config.size - 1) / 2) in
  let final_length = config.size - (2 * subvec_steps) in
  let list_subvec =
    time "list repeated subvec build" (fun () ->
        let rec loop steps length values =
          if steps = 0 then values
          else loop (steps - 1) (length - 2) (list_sub values 1 (length - 2))
        in
        loop subvec_steps config.size list_values)
  in
  let array_subvec =
    time "array repeated subvec build" (fun () ->
        let rec loop steps length values =
          if steps = 0 then values
          else loop (steps - 1) (length - 2) (Array.sub values 1 (length - 2))
        in
        loop subvec_steps config.size array_values)
  in
  let dynarray_subvec =
    time "Dynarray repeated subvec build" (fun () ->
        let rec loop steps length values =
          if steps = 0 then values
          else loop (steps - 1) (length - 2) (dynarray_sub values 1 (length - 2))
        in
        loop subvec_steps config.size dynarray_values)
  in
  let ivector_subvec =
    time "Ivector repeated subvec build" (fun () ->
        let rec loop steps values =
          if steps = 0 then values
          else
            let length = Ivector.length values in
            loop (steps - 1) (Ivector.subvec values 1 (length - 1))
        in
        loop subvec_steps ivector_values)
  in
  check "list repeated subvec length" final_length (List.length list_subvec);
  check "array repeated subvec length" final_length (Array.length array_subvec);
  check "Dynarray repeated subvec length" final_length
    (Dynarray.length dynarray_subvec);
  check "Ivector repeated subvec length" final_length
    (Ivector.length ivector_subvec);
  bench_read_write_after "repeated subvec" config final_length
    (list_subvec, array_subvec, dynarray_subvec, ivector_subvec)

let bench_deep_concat config =
  let check name expected actual =
    if expected <> actual then failwith (name ^ ": unexpected value")
  in
  let size = min config.size 100_000 in
  let expected_sum = size * (size - 1) / 2 in
  let values =
    time "Ivector deep concat build" (fun () ->
        let rec loop i values =
          if i = size then values
          else loop (i + 1) (Ivector.concat values (Ivector.push Ivector.empty i))
        in
        loop 0 Ivector.empty)
  in
  check "Ivector deep concat length" size (Ivector.length values);
  check "Ivector deep concat sequential read" expected_sum
    (time "Ivector deep concat sequential read" (fun () -> sum_ivector values));
  let values_list =
    time "Ivector deep concat to_list" (fun () -> Ivector.to_list values)
  in
  check "Ivector deep concat to_list length" size (List.length values_list);
  check "Ivector deep concat to_list sum" expected_sum
    (List.fold_left ( + ) 0 values_list)

let bench_push_pop config =
  ignore
    (time "Dynarray push then pop" (fun () ->
         let values = Dynarray.create () in
         for i = 0 to config.size - 1 do
           Dynarray.add_last values i
         done;
         for _ = 1 to config.size do
           Dynarray.remove_last values
         done;
         values));
  ignore
    (time "Ivector push then pop" (fun () ->
         let rec push_loop i values =
           if i = config.size then values else push_loop (i + 1) (Ivector.push values i)
         in
         let rec pop_loop values =
           if Ivector.is_empty values then values else pop_loop (Ivector.pop values)
         in
         pop_loop (push_loop 0 Ivector.empty)))

let () =
  let config = parse_config () in
  if config.size <= 0 || config.reads < 0 || config.updates < 0 then
    invalid_arg "benchmark sizes must be positive";
  Printf.printf "size=%d reads=%d updates=%d\n" config.size config.reads
    config.updates;
  Printf.printf
    "Note: list and Ivector update benchmarks are persistent; array and Dynarray \
     updates are mutable.\n\n";
  let values = bench_build config in
  print_endline "";
  bench_sequential_read values;
  print_endline "";
  bench_random_read config values;
  print_endline "";
  bench_updates config values;
  print_endline "";
  bench_subvec_concat config values;
  print_endline "";
  bench_repeated_concat_subvec config values;
  print_endline "";
  bench_deep_concat config;
  print_endline "";
  bench_push_pop config
