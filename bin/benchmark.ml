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
    (time "Ivector sequential read" (fun () ->
         let sum = ref 0 in
         for i = 0 to Ivector.length ivector_values - 1 do
           sum := !sum + Ivector.get ivector_values i
         done;
         !sum));
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
  bench_push_pop config
