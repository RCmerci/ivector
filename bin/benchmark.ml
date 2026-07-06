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
  current_measurements :=
    { name; elapsed_ms = elapsed *. 1000.0 } :: !current_measurements;
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

let ivector_random_sum values indices =
  Array.fold_left (fun acc index -> acc + Ivector.get values index) 0 indices

let rrbvec_random_sum values indices =
  Array.fold_left (fun acc index -> acc + Rrbvec.get values index) 0 indices

let batvect_random_sum values indices =
  Array.fold_left (fun acc index -> acc + BatVect.get values index) 0 indices

let array_push_front values value = Array.append [| value |] values

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

let batvect_sub values start length =
  BatVect.sub values start length

let concat_nonempty combine = function
  | [] -> invalid_arg "expected at least one chunk"
  | first :: rest -> List.fold_left combine first rest

let sum_array values = Array.fold_left ( + ) 0 values

let sum_ivector values = Ivector.fold_left ( + ) 0 values

let check_ivector_invariants name values =
  try Ivector.invariants values
  with exn ->
    failwith
      (Printf.sprintf "%s: Ivector invariant failure: %s" name
         (Printexc.to_string exn))

let sum_rrbvec values = Rrbvec.fold_left ( + ) 0 values

let check_rrbvec_invariants name values =
  try Rrbvec.invariants values
  with exn ->
    failwith
      (Printf.sprintf "%s: Rrbvec invariant failure: %s" name
         (Printexc.to_string exn))

let sum_batvect values = BatVect.fold_left ( + ) 0 values

let update_array values indices =
  let values = Array.copy values in
  Array.iteri (fun i index -> values.(index) <- -(i + 1)) indices;
  values

let update_list values indices =
  let values = ref values in
  Array.iteri (fun i index -> values := list_set index (-(i + 1)) !values) indices;
  !values

let update_ivector values indices =
  let values = ref values in
  Array.iteri (fun i index -> values := Ivector.set !values index (-(i + 1))) indices;
  !values

let update_rrbvec values indices =
  let values = ref values in
  Array.iteri (fun i index -> values := Rrbvec.set !values index (-(i + 1))) indices;
  !values

let update_batvect values indices =
  let values = ref values in
  Array.iteri (fun i index -> values := BatVect.set !values index (-(i + 1))) indices;
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
  let ivector_values =
    time "Ivector build (push)" (fun () ->
        let rec loop i values =
          if i = config.size then values else loop (i + 1) (Ivector.push values i)
        in
        loop 0 Ivector.empty)
  in
  let rrbvec_values =
    time "Rrbvec build (push)" (fun () ->
        let rec loop i values =
          if i = config.size then values else loop (i + 1) (Rrbvec.push_back values i)
        in
        loop 0 Rrbvec.empty)
  in
  let batvect_values =
    time "BatVect build (append)" (fun () ->
        let rec loop i values =
          if i = config.size then values else loop (i + 1) (BatVect.append i values)
        in
        loop 0 BatVect.empty)
  in
  let list_push_front_values =
    time "list build (push_front)" (fun () ->
        let rec loop i values =
          if i = config.size then values else loop (i + 1) (i :: values)
        in
        loop 0 [])
  in
  let array_push_front_values =
    time "array build (push_front)" (fun () ->
        let rec loop i values =
          if i = config.size then values
          else loop (i + 1) (array_push_front values i)
        in
        loop 0 [||])
  in
  let ivector_push_front_values =
    time "Ivector build (push_front via concat)" (fun () ->
        let rec loop i values =
          if i = config.size then values
          else
            loop (i + 1)
              (Ivector.concat (Ivector.push Ivector.empty i) values)
        in
        loop 0 Ivector.empty)
  in
  let rrbvec_push_front_values =
    time "Rrbvec build (push_front)" (fun () ->
        let rec loop i values =
          if i = config.size then values else loop (i + 1) (Rrbvec.push_front values i)
        in
        loop 0 Rrbvec.empty)
  in
  let batvect_push_front_values =
    time "BatVect build (push_front)" (fun () ->
        let rec loop i values =
          if i = config.size then values else loop (i + 1) (BatVect.prepend i values)
        in
        loop 0 BatVect.empty)
  in
  let ivector_append_list_values =
    time "Ivector build (append_list)" (fun () ->
        Ivector.append_list Ivector.empty list_values)
  in
  let rrbvec_append_list_values =
    time "Rrbvec build (append_list)" (fun () ->
        Rrbvec.append_list Rrbvec.empty list_values)
  in
  let batvect_of_list_values =
    time "BatVect build (of_list)" (fun () -> BatVect.of_list list_values)
  in
  check_ivector_invariants "Ivector build (push)" ivector_values;
  check_ivector_invariants "Ivector build (append_list)" ivector_append_list_values;
  check_ivector_invariants "Ivector build (push_front via concat)" ivector_push_front_values;
  check_rrbvec_invariants "Rrbvec build (push)" rrbvec_values;
  check_rrbvec_invariants "Rrbvec build (append_list)" rrbvec_append_list_values;
  check_rrbvec_invariants "Rrbvec build (push_front)" rrbvec_push_front_values;
  let expected_sum = sum_array array_values in
  let check_length_and_sum name length sum =
    if length <> config.size then failwith (name ^ ": unexpected length");
    if sum <> expected_sum then failwith (name ^ ": unexpected sum")
  in
  check_length_and_sum "list build (push_front)"
    (List.length list_push_front_values)
    (List.fold_left ( + ) 0 list_push_front_values);
  check_length_and_sum "array build (push_front)"
    (Array.length array_push_front_values)
    (sum_array array_push_front_values);
  check_length_and_sum "Ivector build (push_front via concat)"
    (Ivector.length ivector_push_front_values)
    (sum_ivector ivector_push_front_values);
  check_length_and_sum "Rrbvec build (push_front)"
    (Rrbvec.length rrbvec_push_front_values)
    (sum_rrbvec rrbvec_push_front_values);
  check_length_and_sum "BatVect build (push_front)"
    (BatVect.length batvect_push_front_values)
    (sum_batvect batvect_push_front_values);
  if Ivector.length ivector_append_list_values <> config.size then
    failwith "Ivector build (append_list): unexpected length";
  if sum_ivector ivector_append_list_values <> sum_ivector ivector_values then
    failwith "Ivector build (append_list): unexpected sum";
  if Rrbvec.length rrbvec_append_list_values <> config.size then
    failwith "Rrbvec build (append_list): unexpected length";
  if sum_rrbvec rrbvec_append_list_values <> sum_rrbvec rrbvec_values then
    failwith "Rrbvec build (append_list): unexpected sum";
  if BatVect.length batvect_of_list_values <> config.size then
    failwith "BatVect build (of_list): unexpected length";
  if sum_batvect batvect_of_list_values <> sum_batvect batvect_values then
    failwith "BatVect build (of_list): unexpected sum";
  ( list_values,
    array_values,
    ivector_values,
    rrbvec_values,
    batvect_values )

let bench_sequential_read
    ( list_values,
      array_values,
      ivector_values,
      rrbvec_values,
      batvect_values ) =
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
  check "Ivector sequential read" expected
    (time "Ivector sequential read (fold_left)" (fun () ->
         Ivector.fold_left ( + ) 0 ivector_values));
  check "Rrbvec sequential read" expected
    (time "Rrbvec sequential read (fold_left)" (fun () ->
         Rrbvec.fold_left ( + ) 0 rrbvec_values));
  check "Rrbvec reverse sequential read" expected
    (time "Rrbvec reverse sequential read (fold_right)" (fun () ->
         Rrbvec.fold_right ( + ) rrbvec_values 0));
  check "BatVect sequential read" expected
    (time "BatVect sequential read (fold_left)" (fun () ->
         BatVect.fold_left ( + ) 0 batvect_values));
  check "list sequential read" expected
    (time "list sequential read" (fun () -> List.fold_left ( + ) 0 list_values))

let bench_random_read config
    ( _list_values,
      array_values,
      ivector_values,
      rrbvec_values,
      batvect_values ) =
  let indices = make_indices config.reads config.size in
  let expected = array_random_sum array_values indices in
  let check name actual =
    if expected <> actual then failwith (name ^ ": unexpected sum")
  in
  check "array random read"
    (time "array random read" (fun () -> array_random_sum array_values indices));
  check "Ivector random read"
    (time "Ivector random read" (fun () -> ivector_random_sum ivector_values indices));
  check "Rrbvec random read"
    (time "Rrbvec random read" (fun () -> rrbvec_random_sum rrbvec_values indices));
  check "BatVect random read"
    (time "BatVect random read" (fun () -> batvect_random_sum batvect_values indices));
  check "list random read"
    (time "list random read (List.nth)" (fun () ->
         list_random_sum _list_values indices))

let bench_updates config
    ( list_values,
      array_values,
      ivector_values,
      rrbvec_values,
      batvect_values ) =
  let indices = make_indices config.updates config.size in
  ignore
    (time "array mutable set" (fun () ->
         let values = Array.copy array_values in
         Array.iteri (fun i index -> values.(index) <- -i) indices;
         values));
  let ivector_updated =
    time "Ivector persistent set" (fun () ->
         Array.fold_left
           (fun values index -> Ivector.set values index (-index))
           ivector_values indices)
  in
  check_ivector_invariants "Ivector persistent set" ivector_updated;
  let rrbvec_updated =
    time "Rrbvec persistent set" (fun () ->
         Array.fold_left
           (fun values index -> Rrbvec.set values index (-index))
           rrbvec_values indices)
  in
  check_rrbvec_invariants "Rrbvec persistent set" rrbvec_updated;
  ignore
    (time "BatVect persistent set" (fun () ->
         Array.fold_left
           (fun values index -> BatVect.set values index (-index))
           batvect_values indices));
  ignore
    (time "list persistent set" (fun () ->
         Array.fold_left
           (fun values index -> list_set index (-index) values)
           list_values indices))

let bench_subvec_concat config
    ( list_values,
      array_values,
      ivector_values,
      rrbvec_values,
      batvect_values ) =
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
  let ivector_slice =
    time "Ivector subvec" (fun () -> Ivector.subvec ivector_values start stop)
  in
  check_ivector_invariants "Ivector subvec" ivector_slice;
  check "Ivector subvec length" slice_length (Ivector.length ivector_slice);
  check "Ivector subvec sum" expected_slice_sum (sum_ivector ivector_slice);
  let rrbvec_slice =
    time "Rrbvec subvec" (fun () -> Rrbvec.subvec rrbvec_values start stop)
  in
  check_rrbvec_invariants "Rrbvec subvec" rrbvec_slice;
  check "Rrbvec subvec length" slice_length (Rrbvec.length rrbvec_slice);
  check "Rrbvec subvec sum" expected_slice_sum (sum_rrbvec rrbvec_slice);
  let batvect_slice =
    time "BatVect subvec" (fun () -> batvect_sub batvect_values start slice_length)
  in
  check "BatVect subvec length" slice_length (BatVect.length batvect_slice);
  check "BatVect subvec sum" expected_slice_sum (sum_batvect batvect_slice);
  let half = config.size / 2 in
  let list_left = list_sub list_values 0 half in
  let list_right = list_sub list_values half (config.size - half) in
  let array_left = Array.sub array_values 0 half in
  let array_right = Array.sub array_values half (config.size - half) in
  let ivector_left = Ivector.subvec ivector_values 0 half in
  let ivector_right = Ivector.subvec ivector_values half config.size in
  check_ivector_invariants "Ivector concat left" ivector_left;
  check_ivector_invariants "Ivector concat right" ivector_right;
  let rrbvec_left = Rrbvec.subvec rrbvec_values 0 half in
  let rrbvec_right = Rrbvec.subvec rrbvec_values half config.size in
  check_rrbvec_invariants "Rrbvec concat left" rrbvec_left;
  check_rrbvec_invariants "Rrbvec concat right" rrbvec_right;
  let batvect_left = batvect_sub batvect_values 0 half in
  let batvect_right = batvect_sub batvect_values half (config.size - half) in
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
  let ivector_concat =
    time "Ivector concat" (fun () -> Ivector.concat ivector_left ivector_right)
  in
  check_ivector_invariants "Ivector concat" ivector_concat;
  check "Ivector concat length" config.size (Ivector.length ivector_concat);
  check "Ivector concat sum" expected_concat_sum (sum_ivector ivector_concat);
  let rrbvec_concat =
    time "Rrbvec concat" (fun () -> Rrbvec.concat rrbvec_left rrbvec_right)
  in
  check_rrbvec_invariants "Rrbvec concat" rrbvec_concat;
  check "Rrbvec concat length" config.size (Rrbvec.length rrbvec_concat);
  check "Rrbvec concat sum" expected_concat_sum (sum_rrbvec rrbvec_concat);
  let batvect_concat =
    time "BatVect concat" (fun () -> BatVect.concat batvect_left batvect_right)
  in
  check "BatVect concat length" config.size (BatVect.length batvect_concat);
  check "BatVect concat sum" expected_concat_sum (sum_batvect batvect_concat)

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
    ( list_values,
      array_values,
      ivector_values,
      rrbvec_values,
      batvect_values ) =
  let check name expected actual =
    if expected <> actual then failwith (name ^ ": unexpected value")
  in
  check_ivector_invariants ("Ivector " ^ label) ivector_values;
  check_rrbvec_invariants ("Rrbvec " ^ label) rrbvec_values;
  let expected_sequential_sum = sum_array array_values in
  check ("array " ^ label ^ " sequential read") expected_sequential_sum
    (time ("array " ^ label ^ " sequential read") (fun () ->
         sum_array array_values));
  check ("Ivector " ^ label ^ " sequential read") expected_sequential_sum
    (time ("Ivector " ^ label ^ " sequential read") (fun () ->
         sum_ivector ivector_values));
  check ("Rrbvec " ^ label ^ " sequential read") expected_sequential_sum
    (time ("Rrbvec " ^ label ^ " sequential read") (fun () ->
         sum_rrbvec rrbvec_values));
  check ("BatVect " ^ label ^ " sequential read") expected_sequential_sum
    (time ("BatVect " ^ label ^ " sequential read") (fun () ->
         sum_batvect batvect_values));
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
  let rrbvec_list =
    time ("Rrbvec " ^ label ^ " to_list") (fun () ->
        Rrbvec.to_list rrbvec_values)
  in
  check ("Rrbvec " ^ label ^ " to_list length") length (List.length rrbvec_list);
  check ("Rrbvec " ^ label ^ " to_list sum") expected_sequential_sum
    (List.fold_left ( + ) 0 rrbvec_list);
  let batvect_list =
    time ("BatVect " ^ label ^ " to_list") (fun () ->
        BatVect.to_list batvect_values)
  in
  check ("BatVect " ^ label ^ " to_list length") length (List.length batvect_list);
  check ("BatVect " ^ label ^ " to_list sum") expected_sequential_sum
    (List.fold_left ( + ) 0 batvect_list);
  let read_indices = make_indices config.reads length in
  let expected_read_sum = array_random_sum array_values read_indices in
  check ("array " ^ label ^ " random read") expected_read_sum
    (time ("array " ^ label ^ " random read") (fun () ->
         array_random_sum array_values read_indices));
  check ("Ivector " ^ label ^ " random read") expected_read_sum
    (time ("Ivector " ^ label ^ " random read") (fun () ->
         ivector_random_sum ivector_values read_indices));
  check ("Rrbvec " ^ label ^ " random read") expected_read_sum
    (time ("Rrbvec " ^ label ^ " random read") (fun () ->
         rrbvec_random_sum rrbvec_values read_indices));
  check ("BatVect " ^ label ^ " random read") expected_read_sum
    (time ("BatVect " ^ label ^ " random read") (fun () ->
         batvect_random_sum batvect_values read_indices));
  check ("list " ^ label ^ " random read") expected_read_sum
    (time ("list " ^ label ^ " random read") (fun () ->
         list_random_sum list_values read_indices));
  let update_indices = make_indices config.updates length in
  let array_updated =
    time ("array " ^ label ^ " set") (fun () ->
        update_array array_values update_indices)
  in
  let expected_update_sum = sum_array array_updated in
  let ivector_updated =
    time ("Ivector " ^ label ^ " set") (fun () ->
        update_ivector ivector_values update_indices)
  in
  check_ivector_invariants ("Ivector " ^ label ^ " set") ivector_updated;
  check ("Ivector " ^ label ^ " set") expected_update_sum
    (sum_ivector ivector_updated);
  let rrbvec_updated =
    time ("Rrbvec " ^ label ^ " set") (fun () ->
        update_rrbvec rrbvec_values update_indices)
  in
  check_rrbvec_invariants ("Rrbvec " ^ label ^ " set") rrbvec_updated;
  check ("Rrbvec " ^ label ^ " set") expected_update_sum
    (sum_rrbvec rrbvec_updated);
  let batvect_updated =
    time ("BatVect " ^ label ^ " set") (fun () ->
        update_batvect batvect_values update_indices)
  in
  check ("BatVect " ^ label ^ " set") expected_update_sum
    (sum_batvect batvect_updated);
  let list_updated =
    time ("list " ^ label ^ " set") (fun () ->
        update_list list_values update_indices)
  in
  check ("list " ^ label ^ " set") expected_update_sum
    (List.fold_left ( + ) 0 list_updated)

let bench_repeated_concat_subvec config
    ( list_values,
      array_values,
      ivector_values,
      rrbvec_values,
      batvect_values ) =
  let check name expected actual =
    if expected <> actual then failwith (name ^ ": unexpected value")
  in
  run_group "Repeated concat" (fun () ->
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
      let ivector_concat =
        time "Ivector repeated concat build" (fun () ->
            bounds
            |> List.map (fun (start, length) ->
                   Ivector.subvec ivector_values start (start + length))
            |> concat_nonempty Ivector.concat)
      in
      let rrbvec_concat =
        time "Rrbvec repeated concat build" (fun () ->
            bounds
            |> List.map (fun (start, length) ->
                   Rrbvec.subvec rrbvec_values start (start + length))
            |> concat_nonempty Rrbvec.concat)
      in
      let batvect_concat =
        time "BatVect repeated concat build" (fun () ->
            bounds
            |> List.map (fun (start, length) ->
                   batvect_sub batvect_values start length)
            |> concat_nonempty BatVect.concat)
      in
      check_ivector_invariants "Ivector repeated concat build" ivector_concat;
      check_rrbvec_invariants "Rrbvec repeated concat build" rrbvec_concat;
      check "list repeated concat length" config.size (List.length list_concat);
      check "array repeated concat length" config.size (Array.length array_concat);
      check "Ivector repeated concat length" config.size
        (Ivector.length ivector_concat);
      check "Rrbvec repeated concat length" config.size
        (Rrbvec.length rrbvec_concat);
      check "BatVect repeated concat length" config.size
        (BatVect.length batvect_concat);
      bench_read_write_after "repeated concat" config config.size
        ( list_concat,
          array_concat,
          ivector_concat,
          rrbvec_concat,
          batvect_concat ));
  run_group "Repeated subvec" (fun () ->
      let subvec_steps = min 8 ((config.size - 1) / 2) in
      let final_length = config.size - (2 * subvec_steps) in
      let list_subvec =
        time "list repeated subvec build" (fun () ->
            let rec loop steps length values =
              if steps = 0 then values
              else
                loop (steps - 1) (length - 2) (list_sub values 1 (length - 2))
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
      let rrbvec_subvec =
        time "Rrbvec repeated subvec build" (fun () ->
            let rec loop steps values =
              if steps = 0 then values
              else
                let length = Rrbvec.length values in
                loop (steps - 1) (Rrbvec.subvec values 1 (length - 1))
            in
            loop subvec_steps rrbvec_values)
      in
      let batvect_subvec =
        time "BatVect repeated subvec build" (fun () ->
            let rec loop steps values =
              if steps = 0 then values
              else
                let length = BatVect.length values in
                loop (steps - 1) (batvect_sub values 1 (length - 2))
            in
            loop subvec_steps batvect_values)
      in
      check_ivector_invariants "Ivector repeated subvec build" ivector_subvec;
      check_rrbvec_invariants "Rrbvec repeated subvec build" rrbvec_subvec;
      check "list repeated subvec length" final_length (List.length list_subvec);
      check "array repeated subvec length" final_length (Array.length array_subvec);
      check "Ivector repeated subvec length" final_length
        (Ivector.length ivector_subvec);
      check "Rrbvec repeated subvec length" final_length
        (Rrbvec.length rrbvec_subvec);
      check "BatVect repeated subvec length" final_length
        (BatVect.length batvect_subvec);
      bench_read_write_after "repeated subvec" config final_length
        ( list_subvec,
          array_subvec,
          ivector_subvec,
          rrbvec_subvec,
          batvect_subvec ))

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
  let rrbvec_values =
    time "Rrbvec deep concat build" (fun () ->
        let rec loop i values =
          if i = size then values
          else loop (i + 1) (Rrbvec.concat values (Rrbvec.push_back Rrbvec.empty i))
        in
        loop 0 Rrbvec.empty)
  in
  let batvect_values =
    time "BatVect deep concat build" (fun () ->
        let rec loop i values =
          if i = size then values
          else loop (i + 1) (BatVect.concat values (BatVect.append i BatVect.empty))
        in
        loop 0 BatVect.empty)
  in
  check_ivector_invariants "Ivector deep concat build" values;
  check_rrbvec_invariants "Rrbvec deep concat build" rrbvec_values;
  check "Ivector deep concat length" size (Ivector.length values);
  check "Rrbvec deep concat length" size (Rrbvec.length rrbvec_values);
  check "BatVect deep concat length" size (BatVect.length batvect_values);
  check "Ivector deep concat sequential read" expected_sum
    (time "Ivector deep concat sequential read" (fun () -> sum_ivector values));
  check "Rrbvec deep concat sequential read" expected_sum
    (time "Rrbvec deep concat sequential read" (fun () -> sum_rrbvec rrbvec_values));
  check "BatVect deep concat sequential read" expected_sum
    (time "BatVect deep concat sequential read" (fun () ->
         sum_batvect batvect_values));
  let values_list =
    time "Ivector deep concat to_list" (fun () -> Ivector.to_list values)
  in
  check "Ivector deep concat to_list length" size (List.length values_list);
  check "Ivector deep concat to_list sum" expected_sum
    (List.fold_left ( + ) 0 values_list);
  let rrbvec_values_list =
    time "Rrbvec deep concat to_list" (fun () -> Rrbvec.to_list rrbvec_values)
  in
  check "Rrbvec deep concat to_list length" size (List.length rrbvec_values_list);
  check "Rrbvec deep concat to_list sum" expected_sum
    (List.fold_left ( + ) 0 rrbvec_values_list);
  let batvect_values_list =
    time "BatVect deep concat to_list" (fun () -> BatVect.to_list batvect_values)
  in
  check "BatVect deep concat to_list length" size (List.length batvect_values_list);
  check "BatVect deep concat to_list sum" expected_sum
    (List.fold_left ( + ) 0 batvect_values_list)

let bench_push_pop config =
  let ivector_after_push_pop =
    time "Ivector push then pop" (fun () ->
         let rec push_loop i values =
           if i = config.size then values else push_loop (i + 1) (Ivector.push values i)
         in
         let rec pop_loop values =
           if Ivector.is_empty values then values else pop_loop (Ivector.pop values)
        in
        pop_loop (push_loop 0 Ivector.empty))
  in
  check_ivector_invariants "Ivector push then pop" ivector_after_push_pop;
  let rrbvec_after_push_pop =
    time "Rrbvec push then pop" (fun () ->
         let rec push_loop i values =
           if i = config.size then values
           else push_loop (i + 1) (Rrbvec.push_back values i)
         in
         let rec pop_loop values =
           if Rrbvec.is_empty values then values else pop_loop (snd (Rrbvec.pop_back values))
        in
        pop_loop (push_loop 0 Rrbvec.empty))
  in
  check_rrbvec_invariants "Rrbvec push then pop" rrbvec_after_push_pop;
  ignore
    (time "BatVect append then pop" (fun () ->
         let rec push_loop i values =
           if i = config.size then values else push_loop (i + 1) (BatVect.append i values)
         in
         let rec pop_loop values =
           if BatVect.is_empty values then values else pop_loop (snd (BatVect.pop values))
         in
         pop_loop (push_loop 0 BatVect.empty)))

let () =
  let config = parse_config () in
  if config.size <= 0 || config.reads < 0 || config.updates < 0 then
    invalid_arg "benchmark sizes must be positive";
  Printf.printf "size=%d reads=%d updates=%d\n" config.size config.reads
    config.updates;
  Printf.printf
    "Note: list, Ivector, Rrbvec, and BatVect update benchmarks are persistent; \
     array updates are mutable.\n\n";
  let values = run_group "Build" (fun () -> bench_build config) in
  run_group "Sequential read" (fun () -> bench_sequential_read values);
  run_group "Random read" (fun () -> bench_random_read config values);
  run_group "Updates" (fun () -> bench_updates config values);
  run_group "Subvec and concat" (fun () -> bench_subvec_concat config values);
  bench_repeated_concat_subvec config values;
  run_group "Deep concat" (fun () -> bench_deep_concat config);
  run_group "Push/pop" (fun () -> bench_push_pop config)
