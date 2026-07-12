module B = Bechamel.Benchmark
module A = Bechamel.Analyze
module M = Bechamel.Measure
module S = Bechamel.Staged
module T = Bechamel.Test
module Time = Bechamel.Time
module Toolkit = Bechamel.Toolkit

let default_size = 50_000
let default_reads = 10_000
let default_updates = 5_000
let default_limit = 200
let default_quota_ms = 20.0

type config = {
  size : int;
  reads : int;
  updates : int;
  limit : int;
  quota_ms : float;
}

type values = {
  rrbvec : int Rrbvec.t;
  batvect : int BatVect.t;
}

type case = {
  name : string;
  run : unit -> unit;
}

type group = {
  name : string;
  cases : case list;
}

let paired_group name rrbvec_run batvect_run =
  {
    name;
    cases =
      [
        { name = "Rrbvec"; run = rrbvec_run };
        { name = "BatVect"; run = batvect_run };
      ];
  }

type result = {
  name : string;
  estimated_ms : float option;
  r_square : float option;
  samples : int option;
}

let parse_config () =
  let size = ref default_size in
  let reads = ref default_reads in
  let updates = ref default_updates in
  let limit = ref default_limit in
  let quota_ms = ref default_quota_ms in
  let spec =
    [
      ("--size", Arg.Set_int size, "Number of elements to build");
      ("--reads", Arg.Set_int reads, "Number of indexed reads");
      ("--updates", Arg.Set_int updates, "Number of random indexed writes");
      ("--limit", Arg.Set_int limit, "Maximum Bechamel samples per benchmark");
      ("--quota-ms", Arg.Set_float quota_ms, "Maximum Bechamel time per benchmark in milliseconds");
    ]
  in
  Arg.parse spec
    (fun arg -> raise (Arg.Bad ("unexpected argument: " ^ arg)))
    "rrbvec-bench [--size N] [--reads N] [--updates N] [--limit N] [--quota-ms N]";
  { size = !size; reads = !reads; updates = !updates; limit = !limit; quota_ms = !quota_ms }

let check name expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "%s: expected %d, got %d" name expected actual)

let check_bool name expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "%s: expected %b, got %b" name expected actual)

let check_int_option name expected actual =
  if expected <> actual then
    let show = function None -> "None" | Some value -> "Some " ^ string_of_int value in
    failwith
      (Printf.sprintf "%s: expected %s, got %s" name (show expected)
         (show actual))

let make_indices count modulo_by =
  Array.init count (fun i -> (i * 1_103 + 12_345) mod modulo_by)

let range_sum start length = (start + start + length - 1) * length / 2

let sum_rrbvec values = Rrbvec.fold_left ( + ) 0 values
let sum_batvect values = BatVect.fold_left ( + ) 0 values
let sum_list values = List.fold_left ( + ) 0 values
let sum_array values = Array.fold_left ( + ) 0 values
let map_value value = (value * 2) + 1
let map_rrbvec values = Rrbvec.map map_value values
let map_batvect values = BatVect.map map_value values
let keep_value value = value mod 3 <> 1
let filter_map_value value = if value mod 4 = 0 then Some (value / 2) else None
let mapi_value index value = index + value + 1
let public_api_for_all_value value = value >= 0

let sum_rrbvec_iter values =
  let sum = ref 0 in
  Rrbvec.iter (fun value -> sum := !sum + value) values;
  !sum

let sum_batvect_iter values =
  let sum = ref 0 in
  BatVect.iter (fun value -> sum := !sum + value) values;
  !sum

let sum_rrbvec_iteri values =
  let sum = ref 0 in
  Rrbvec.iteri (fun index value -> sum := !sum + index + value) values;
  !sum

let sum_batvect_iteri values =
  let sum = ref 0 in
  BatVect.iteri (fun index value -> sum := !sum + index + value) values;
  !sum

let sum_rrbvec_iter2 left right =
  let sum = ref 0 in
  Rrbvec.iter2 (fun left right -> sum := !sum + left + right) left right;
  !sum

let filter_rrbvec values = Rrbvec.filter keep_value values
let filter_batvect values = BatVect.filter keep_value values
let filter_map_rrbvec values = Rrbvec.filter_map filter_map_value values
let filter_map_batvect values = BatVect.filter_map filter_map_value values
let mapi_rrbvec values = Rrbvec.mapi mapi_value values
let mapi_batvect values = BatVect.mapi mapi_value values
let partition_rrbvec values = Rrbvec.partition keep_value values
let partition_batvect values = BatVect.partition keep_value values

let concat_map_singleton values = Rrbvec.concat_map Rrbvec.singleton values

let concat_map_pair values =
  Rrbvec.concat_map (fun value -> Rrbvec.of_array [| value; -value |]) values

let concat_map_mostly_empty values =
  Rrbvec.concat_map
    (fun value -> if value mod 10 = 0 then Rrbvec.singleton value else Rrbvec.empty)
    values

let concat_map_constant mapped values =
  Rrbvec.concat_map (fun _ -> mapped) values

let check_rrbvec_invariants name values =
  try Rrbvec.Private.invariants values
  with exn ->
    failwith
      (Printf.sprintf "%s: Rrbvec invariant failure: %s" name
         (Printexc.to_string exn))

let rrbvec_nth values index = Rrbvec.nth values index

let rrbvec_pop_back values =
  match Rrbvec.pop_back values with
  | Some result -> result
  | None -> invalid_arg "Rrbvec.pop_back returned None"

let rrbvec_pop_front values =
  match Rrbvec.pop_front values with
  | Some result -> result
  | None -> invalid_arg "Rrbvec.pop_front returned None"

let rrbvec_subvec values start stop =
  match Rrbvec.subvec values start stop with
  | Some values -> values
  | None -> invalid_arg "Rrbvec.subvec returned None"

let batvect_sub values start length = BatVect.sub values start length

let rrbvec_random_sum values indices =
  Array.fold_left (fun acc index -> acc + rrbvec_nth values index) 0 indices

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

let build_rrbvec size =
  let rec loop i values =
    if i = size then values else loop (i + 1) (Rrbvec.push_back values i)
  in
  loop 0 Rrbvec.empty

let build_batvect size =
  let rec loop i values =
    if i = size then values else loop (i + 1) (BatVect.append i values)
  in
  loop 0 BatVect.empty

let build_rrbvec_front size =
  let rec loop i values =
    if i = size then values else loop (i + 1) (Rrbvec.push_front values i)
  in
  loop 0 Rrbvec.empty

let build_batvect_front size =
  let rec loop i values =
    if i = size then values else loop (i + 1) (BatVect.prepend i values)
  in
  loop 0 BatVect.empty

let pop_back_rrbvec values =
  let rec loop values =
    if Rrbvec.is_empty values then values else loop (snd (rrbvec_pop_back values))
  in
  loop values

let pop_front_rrbvec values =
  let rec loop values =
    if Rrbvec.is_empty values then values else loop (snd (rrbvec_pop_front values))
  in
  loop values

let pop_back_batvect values =
  let rec loop values =
    if BatVect.is_empty values then values else loop (snd (BatVect.pop values))
  in
  loop values

let pop_front_batvect values =
  let rec loop values =
    if BatVect.is_empty values then values else loop (snd (BatVect.shift values))
  in
  loop values

let repeated_rrbvec_subvec steps values =
  let rec loop steps values =
    if steps = 0 then values
    else
      let length = Rrbvec.length values in
      loop (steps - 1) (rrbvec_subvec values 1 (length - 1))
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

let push_pop_rrbvec size =
  let rec push_loop i values =
    if i = size then values else push_loop (i + 1) (Rrbvec.push_back values i)
  in
  let rec pop_loop values =
    if Rrbvec.is_empty values then values
    else pop_loop (snd (rrbvec_pop_back values))
  in
  pop_loop (push_loop 0 Rrbvec.empty)

let push_pop_batvect size =
  let rec push_loop i values =
    if i = size then values else push_loop (i + 1) (BatVect.append i values)
  in
  let rec pop_loop values =
    if BatVect.is_empty values then values else pop_loop (snd (BatVect.pop values))
  in
  pop_loop (push_loop 0 BatVect.empty)

let prepare_values config =
  let rrbvec = build_rrbvec config.size in
  let batvect = build_batvect config.size in
  check_rrbvec_invariants "Rrbvec sequential write (push_back)" rrbvec;
  let expected_sum = range_sum 0 config.size in
  check "Rrbvec sequential write length" config.size (Rrbvec.length rrbvec);
  check "BatVect sequential write length" config.size (BatVect.length batvect);
  check "Rrbvec sequential write sum" expected_sum (sum_rrbvec rrbvec);
  check "BatVect sequential write sum" expected_sum (sum_batvect batvect);
  { rrbvec; batvect }

let verify_front_writes config =
  let rrbvec = build_rrbvec_front config.size in
  let batvect = build_batvect_front config.size in
  check_rrbvec_invariants "Rrbvec sequential write (push_front)" rrbvec;
  let expected_sum = range_sum 0 config.size in
  check "Rrbvec sequential write push_front length" config.size (Rrbvec.length rrbvec);
  check "BatVect sequential write push_front length" config.size (BatVect.length batvect);
  check "Rrbvec sequential write push_front sum" expected_sum (sum_rrbvec rrbvec);
  check "BatVect sequential write push_front sum" expected_sum (sum_batvect batvect)

let verify_sequential_pops values =
  let rrbvec_back = pop_back_rrbvec values.rrbvec in
  let rrbvec_front = pop_front_rrbvec values.rrbvec in
  let batvect_back = pop_back_batvect values.batvect in
  let batvect_front = pop_front_batvect values.batvect in
  check_rrbvec_invariants "Rrbvec sequential pop_back" rrbvec_back;
  check_rrbvec_invariants "Rrbvec sequential pop_front" rrbvec_front;
  check "Rrbvec sequential pop_back length" 0 (Rrbvec.length rrbvec_back);
  check "Rrbvec sequential pop_front length" 0 (Rrbvec.length rrbvec_front);
  check "BatVect sequential pop_back length" 0 (BatVect.length batvect_back);
  check "BatVect sequential pop_front length" 0 (BatVect.length batvect_front)

let verify_random_write config values indices =
  let expected = expected_update_sum config.size indices in
  let rrbvec_updated = update_rrbvec values.rrbvec indices in
  let batvect_updated = update_batvect values.batvect indices in
  check_rrbvec_invariants "Rrbvec random write (set)" rrbvec_updated;
  check "Rrbvec random write (set)" expected (sum_rrbvec rrbvec_updated);
  check "BatVect random write (set)" expected (sum_batvect batvect_updated)

let verify_map config values =
  let expected_sum = (2 * range_sum 0 config.size) + config.size in
  let rrbvec_mapped = map_rrbvec values.rrbvec in
  let batvect_mapped = map_batvect values.batvect in
  check_rrbvec_invariants "Rrbvec map" rrbvec_mapped;
  check "Rrbvec map length" config.size (Rrbvec.length rrbvec_mapped);
  check "BatVect map length" config.size (BatVect.length batvect_mapped);
  check "Rrbvec map sum" expected_sum (sum_rrbvec rrbvec_mapped);
  check "BatVect map sum" expected_sum (sum_batvect batvect_mapped)

let verify_conversions config values =
  let list_values = List.init config.size Fun.id in
  let array_values = Array.init config.size Fun.id in
  let expected_sum = range_sum 0 config.size in
  let rrbvec_from_list = Rrbvec.of_list list_values in
  let batvect_from_list = BatVect.of_list list_values in
  let rrbvec_from_array = Rrbvec.of_array array_values in
  let batvect_from_array = BatVect.of_array array_values in
  check_rrbvec_invariants "Rrbvec of_list" rrbvec_from_list;
  check_rrbvec_invariants "Rrbvec of_array" rrbvec_from_array;
  check "Rrbvec of_list length" config.size (Rrbvec.length rrbvec_from_list);
  check "BatVect of_list length" config.size (BatVect.length batvect_from_list);
  check "Rrbvec of_array length" config.size (Rrbvec.length rrbvec_from_array);
  check "BatVect of_array length" config.size (BatVect.length batvect_from_array);
  check "Rrbvec of_list sum" expected_sum (sum_rrbvec rrbvec_from_list);
  check "BatVect of_list sum" expected_sum (sum_batvect batvect_from_list);
  check "Rrbvec of_array sum" expected_sum (sum_rrbvec rrbvec_from_array);
  check "BatVect of_array sum" expected_sum (sum_batvect batvect_from_array);
  check "Rrbvec to_list sum" expected_sum (sum_list (Rrbvec.to_list values.rrbvec));
  check "BatVect to_list sum" expected_sum (sum_list (BatVect.to_list values.batvect));
  check "Rrbvec to_array sum" expected_sum (sum_array (Rrbvec.to_array values.rrbvec));
  check "BatVect to_array sum" expected_sum (sum_array (BatVect.to_array values.batvect))

let verify_subvec_concat config values =
  let subvec_steps = min 8 ((config.size - 1) / 2) in
  let final_length = config.size - (2 * subvec_steps) in
  let expected_subvec_sum = range_sum subvec_steps final_length in
  let rrbvec_repeated_subvec =
    repeated_rrbvec_subvec subvec_steps values.rrbvec
  in
  check_rrbvec_invariants "Rrbvec repeated subvec" rrbvec_repeated_subvec;
  check "Rrbvec repeated subvec length" final_length
    (Rrbvec.length rrbvec_repeated_subvec);
  check "Rrbvec repeated subvec sum" expected_subvec_sum
    (sum_rrbvec rrbvec_repeated_subvec);
  let batvect_subvec = repeated_batvect_subvec subvec_steps values.batvect in
  check "BatVect repeated subvec length" final_length (BatVect.length batvect_subvec);
  check "BatVect repeated subvec sum" expected_subvec_sum (sum_batvect batvect_subvec);
  let chunks = min 8 config.size in
  let bounds = chunk_bounds config.size chunks in
  let expected_concat_sum = range_sum 0 config.size in
  let rrbvec_concat =
    bounds
    |> List.map (fun (start, length) ->
           rrbvec_subvec values.rrbvec start (start + length))
    |> concat_nonempty Rrbvec.concat
  in
  check_rrbvec_invariants "Rrbvec repeated concat" rrbvec_concat;
  check "Rrbvec repeated concat length" config.size (Rrbvec.length rrbvec_concat);
  check "Rrbvec repeated concat sum" expected_concat_sum (sum_rrbvec rrbvec_concat);
  let batvect_concat =
    bounds
    |> List.map (fun (start, length) -> batvect_sub values.batvect start length)
    |> concat_nonempty BatVect.concat
  in
  check "BatVect repeated concat length" config.size (BatVect.length batvect_concat);
  check "BatVect repeated concat sum" expected_concat_sum (sum_batvect batvect_concat)

let verify_push_pop config =
  let rrbvec_after_push_pop = push_pop_rrbvec config.size in
  check_rrbvec_invariants "Rrbvec push then pop" rrbvec_after_push_pop;
  ignore (push_pop_batvect config.size)

let verify_public_api config values =
  let last = config.size - 1 in
  let expected_sum = range_sum 0 config.size in
  let expected_mapi_sum = (2 * expected_sum) + config.size in
  check "Rrbvec iter sum" expected_sum (sum_rrbvec_iter values.rrbvec);
  check "BatVect iter sum" expected_sum (sum_batvect_iter values.batvect);
  check "Rrbvec iteri sum" (2 * expected_sum) (sum_rrbvec_iteri values.rrbvec);
  check "BatVect iteri sum" (2 * expected_sum) (sum_batvect_iteri values.batvect);
  let rrbvec_filtered = filter_rrbvec values.rrbvec in
  let batvect_filtered = filter_batvect values.batvect in
  check_rrbvec_invariants "Rrbvec filter" rrbvec_filtered;
  check "filter length" (BatVect.length batvect_filtered)
    (Rrbvec.length rrbvec_filtered);
  check "filter sum" (sum_batvect batvect_filtered)
    (sum_rrbvec rrbvec_filtered);
  let rrbvec_filter_mapped = filter_map_rrbvec values.rrbvec in
  let batvect_filter_mapped = filter_map_batvect values.batvect in
  check_rrbvec_invariants "Rrbvec filter_map" rrbvec_filter_mapped;
  check "filter_map length" (BatVect.length batvect_filter_mapped)
    (Rrbvec.length rrbvec_filter_mapped);
  check "filter_map sum" (sum_batvect batvect_filter_mapped)
    (sum_rrbvec rrbvec_filter_mapped);
  let rrbvec_mapi = mapi_rrbvec values.rrbvec in
  let batvect_mapi = mapi_batvect values.batvect in
  check_rrbvec_invariants "Rrbvec mapi" rrbvec_mapi;
  check "Rrbvec mapi length" config.size (Rrbvec.length rrbvec_mapi);
  check "BatVect mapi length" config.size (BatVect.length batvect_mapi);
  check "Rrbvec mapi sum" expected_mapi_sum (sum_rrbvec rrbvec_mapi);
  check "BatVect mapi sum" expected_mapi_sum (sum_batvect batvect_mapi);
  check_bool "Rrbvec exists" true
    (Rrbvec.exists (fun value -> value = last) values.rrbvec);
  check_bool "BatVect exists" true
    (BatVect.exists (fun value -> value = last) values.batvect);
  check_bool "Rrbvec for_all" true
    (Rrbvec.for_all public_api_for_all_value values.rrbvec);
  check_bool "BatVect for_all" true
    (BatVect.for_all public_api_for_all_value values.batvect);
  check "Rrbvec find" last
    (Rrbvec.find (fun value -> value = last) values.rrbvec);
  check "BatVect find" last
    (BatVect.find (fun value -> value = last) values.batvect);
  check_int_option "Rrbvec find_opt" (Some last)
    (Rrbvec.find_opt (fun value -> value = last) values.rrbvec);
  check_int_option "BatVect find_opt" (Some last)
    (BatVect.find_opt (fun value -> value = last) values.batvect);
  check_bool "Rrbvec mem" true (Rrbvec.mem last values.rrbvec);
  check_bool "BatVect mem" true (BatVect.mem last values.batvect);
  let rrbvec_init = Rrbvec.init config.size Fun.id in
  let batvect_init = BatVect.init config.size Fun.id in
  check_rrbvec_invariants "Rrbvec init" rrbvec_init;
  check "Rrbvec init sum" expected_sum (sum_rrbvec rrbvec_init);
  check "BatVect init sum" expected_sum (sum_batvect batvect_init);
  let rrbvec_partition_left, rrbvec_partition_right =
    partition_rrbvec values.rrbvec
  in
  let batvect_partition_left, batvect_partition_right =
    partition_batvect values.batvect
  in
  check_rrbvec_invariants "Rrbvec partition left" rrbvec_partition_left;
  check_rrbvec_invariants "Rrbvec partition right" rrbvec_partition_right;
  check "partition left length" (BatVect.length batvect_partition_left)
    (Rrbvec.length rrbvec_partition_left);
  check "partition right length" (BatVect.length batvect_partition_right)
    (Rrbvec.length rrbvec_partition_right);
  check "partition left sum" (sum_batvect batvect_partition_left)
    (sum_rrbvec rrbvec_partition_left);
  check "partition right sum" (sum_batvect batvect_partition_right)
    (sum_rrbvec rrbvec_partition_right)

let public_api_benchmark_groups config values =
  let last = config.size - 1 in
  [
    paired_group "Public API/filter"
      (fun () -> ignore (Sys.opaque_identity (filter_rrbvec values.rrbvec)))
      (fun () -> ignore (Sys.opaque_identity (filter_batvect values.batvect)));
    paired_group "Public API/filter_map"
      (fun () -> ignore (Sys.opaque_identity (filter_map_rrbvec values.rrbvec)))
      (fun () -> ignore (Sys.opaque_identity (filter_map_batvect values.batvect)));
    paired_group "Public API/iter"
      (fun () -> ignore (Sys.opaque_identity (sum_rrbvec_iter values.rrbvec)))
      (fun () -> ignore (Sys.opaque_identity (sum_batvect_iter values.batvect)));
    paired_group "Public API/iteri"
      (fun () -> ignore (Sys.opaque_identity (sum_rrbvec_iteri values.rrbvec)))
      (fun () -> ignore (Sys.opaque_identity (sum_batvect_iteri values.batvect)));
    paired_group "Public API/mapi"
      (fun () -> ignore (Sys.opaque_identity (mapi_rrbvec values.rrbvec)))
      (fun () -> ignore (Sys.opaque_identity (mapi_batvect values.batvect)));
    paired_group "Public API/exists"
      (fun () ->
        ignore
          (Sys.opaque_identity
             (Rrbvec.exists (fun value -> value = last) values.rrbvec)))
      (fun () ->
        ignore
          (Sys.opaque_identity
             (BatVect.exists (fun value -> value = last) values.batvect)));
    paired_group "Public API/for_all"
      (fun () ->
        ignore
          (Sys.opaque_identity
             (Rrbvec.for_all public_api_for_all_value values.rrbvec)))
      (fun () ->
        ignore
          (Sys.opaque_identity
             (BatVect.for_all public_api_for_all_value values.batvect)));
    paired_group "Public API/find"
      (fun () ->
        ignore
          (Sys.opaque_identity
             (Rrbvec.find (fun value -> value = last) values.rrbvec)))
      (fun () ->
        ignore
          (Sys.opaque_identity
             (BatVect.find (fun value -> value = last) values.batvect)));
    paired_group "Public API/find_opt"
      (fun () ->
        ignore
          (Sys.opaque_identity
             (Rrbvec.find_opt (fun value -> value = last) values.rrbvec)))
      (fun () ->
        ignore
          (Sys.opaque_identity
             (BatVect.find_opt (fun value -> value = last) values.batvect)));
    paired_group "Public API/mem"
      (fun () -> ignore (Sys.opaque_identity (Rrbvec.mem last values.rrbvec)))
      (fun () -> ignore (Sys.opaque_identity (BatVect.mem last values.batvect)));
    paired_group "Public API/init"
      (fun () -> ignore (Sys.opaque_identity (Rrbvec.init config.size Fun.id)))
      (fun () -> ignore (Sys.opaque_identity (BatVect.init config.size Fun.id)));
    paired_group "Public API/partition"
      (fun () -> ignore (Sys.opaque_identity (partition_rrbvec values.rrbvec)))
      (fun () -> ignore (Sys.opaque_identity (partition_batvect values.batvect)));
    {
      name = "Pairwise API";
      cases =
        [
          {
            name = "Rrbvec map2";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.map2 ( + ) values.rrbvec values.rrbvec)));
          };
          {
            name = "Rrbvec combine";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.combine values.rrbvec values.rrbvec)));
          };
          {
            name = "Rrbvec iter2";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (sum_rrbvec_iter2 values.rrbvec values.rrbvec)));
          };
          {
            name = "Rrbvec fold_left2";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.fold_left2
                        (fun acc left right -> acc + left + right)
                        0 values.rrbvec values.rrbvec)));
          };
          {
            name = "Rrbvec for_all2";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.for_all2 ( = ) values.rrbvec values.rrbvec)));
          };
          {
            name = "Rrbvec exists2";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.exists2
                        (fun left right -> left = last && right = last)
                        values.rrbvec values.rrbvec)));
          };
          {
            name = "Rrbvec fold_right2";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.fold_right2
                        (fun left right acc -> acc + left + right)
                        values.rrbvec values.rrbvec 0)));
          };
          {
            name = "Rrbvec equal";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.equal Int.equal values.rrbvec values.rrbvec)));
          };
          {
            name = "Rrbvec compare";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (Rrbvec.compare Int.compare values.rrbvec values.rrbvec)));
          };
        ];
    };
  ]

let benchmark_groups config values =
  let read_indices = make_indices config.reads config.size in
  let update_indices = make_indices config.updates config.size in
  let subvec_steps = min 8 ((config.size - 1) / 2) in
  let bounds = chunk_bounds config.size (min 8 config.size) in
  let list_values = List.init config.size Fun.id in
  let array_values = Array.init config.size Fun.id in
  let concat_map_singleton_input = Rrbvec.init 20_000 Fun.id in
  let concat_map_pair_input = Rrbvec.init 10_000 Fun.id in
  let concat_map_mostly_empty_input = Rrbvec.init 20_000 Fun.id in
  let concat_map_chunk_input = Rrbvec.init 5_000 Fun.id in
  let concat_map_1024_input = Rrbvec.init 200 Fun.id in
  let concat_map_one_large_input = Rrbvec.singleton 0 in
  let concat_map_two_large_input = Rrbvec.of_array [| 0; 1 |] in
  let concat_map_33_values = Rrbvec.init 33 Fun.id in
  let concat_map_1024_values = Rrbvec.init 1024 Fun.id in
  let concat_map_large_values = Rrbvec.init 1_000_000 Fun.id in
  let base_groups =
    [
      {
        name = "Conversion";
        cases =
          [
            { name = "Rrbvec of_list"; run = (fun () -> ignore (Sys.opaque_identity (Rrbvec.of_list list_values))) };
            { name = "BatVect of_list"; run = (fun () -> ignore (Sys.opaque_identity (BatVect.of_list list_values))) };
            { name = "Rrbvec to_list"; run = (fun () -> ignore (Sys.opaque_identity (Rrbvec.to_list values.rrbvec))) };
            { name = "BatVect to_list"; run = (fun () -> ignore (Sys.opaque_identity (BatVect.to_list values.batvect))) };
            { name = "Rrbvec of_array"; run = (fun () -> ignore (Sys.opaque_identity (Rrbvec.of_array array_values))) };
            { name = "BatVect of_array"; run = (fun () -> ignore (Sys.opaque_identity (BatVect.of_array array_values))) };
            { name = "Rrbvec to_array"; run = (fun () -> ignore (Sys.opaque_identity (Rrbvec.to_array values.rrbvec))) };
            { name = "BatVect to_array"; run = (fun () -> ignore (Sys.opaque_identity (BatVect.to_array values.batvect))) };
          ];
      };
      {
        name = "Sequential write";
        cases =
          [
            { name = "Rrbvec sequential write (push_back)"; run = (fun () -> ignore (Sys.opaque_identity (build_rrbvec config.size))) };
            { name = "BatVect sequential write (append)"; run = (fun () -> ignore (Sys.opaque_identity (build_batvect config.size))) };
            { name = "Rrbvec sequential write (push_front)"; run = (fun () -> ignore (Sys.opaque_identity (build_rrbvec_front config.size))) };
            { name = "BatVect sequential write (push_front)"; run = (fun () -> ignore (Sys.opaque_identity (build_batvect_front config.size))) };
            { name = "Rrbvec sequential pop_back"; run = (fun () -> ignore (Sys.opaque_identity (pop_back_rrbvec values.rrbvec))) };
            { name = "BatVect sequential pop_back"; run = (fun () -> ignore (Sys.opaque_identity (pop_back_batvect values.batvect))) };
            { name = "Rrbvec sequential pop_front"; run = (fun () -> ignore (Sys.opaque_identity (pop_front_rrbvec values.rrbvec))) };
            { name = "BatVect sequential pop_front"; run = (fun () -> ignore (Sys.opaque_identity (pop_front_batvect values.batvect))) };
          ];
      };
      {
        name = "Sequential read";
        cases =
          [
            { name = "Rrbvec sequential read (fold_left)"; run = (fun () -> ignore (Sys.opaque_identity (sum_rrbvec values.rrbvec))) };
            { name = "Rrbvec sequential read (fold_right)"; run = (fun () -> ignore (Sys.opaque_identity (Rrbvec.fold_right ( + ) values.rrbvec 0))) };
            { name = "Rrbvec map"; run = (fun () -> ignore (Sys.opaque_identity (map_rrbvec values.rrbvec))) };
            { name = "BatVect sequential read (fold_left)"; run = (fun () -> ignore (Sys.opaque_identity (sum_batvect values.batvect))) };
            { name = "BatVect sequential read (fold_right)"; run = (fun () -> ignore (Sys.opaque_identity (BatVect.fold_right ( + ) values.batvect 0))) };
            { name = "BatVect map"; run = (fun () -> ignore (Sys.opaque_identity (map_batvect values.batvect))) };
          ];
      };
    ]
  in
  let remaining_groups =
    [
      {
        name = "Random read";
        cases =
          [
            { name = "Rrbvec random read"; run = (fun () -> ignore (Sys.opaque_identity (rrbvec_random_sum values.rrbvec read_indices))) };
            { name = "BatVect random read"; run = (fun () -> ignore (Sys.opaque_identity (batvect_random_sum values.batvect read_indices))) };
          ];
      };
    {
      name = "Random write";
      cases =
        [
          { name = "Rrbvec random write (set)"; run = (fun () -> ignore (Sys.opaque_identity (update_rrbvec values.rrbvec update_indices))) };
          { name = "BatVect random write (set)"; run = (fun () -> ignore (Sys.opaque_identity (update_batvect values.batvect update_indices))) };
        ];
    };
    {
      name = "Subvec and concat";
      cases =
        [
          {
            name = "Rrbvec repeated subvec";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (repeated_rrbvec_subvec subvec_steps values.rrbvec)));
          };
          {
            name = "BatVect repeated subvec";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (repeated_batvect_subvec subvec_steps values.batvect)));
          };
          {
            name = "Rrbvec repeated concat";
            run =
              (fun () ->
                let result =
                  bounds
                  |> List.map (fun (start, length) ->
                         rrbvec_subvec values.rrbvec start (start + length))
                  |> concat_nonempty Rrbvec.concat
                in
                ignore (Sys.opaque_identity result));
          };
          {
            name = "BatVect repeated concat";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (bounds
                     |> List.map (fun (start, length) -> batvect_sub values.batvect start length)
                     |> concat_nonempty BatVect.concat)));
          };
        ];
    };
    {
      name = "Push/pop";
      cases =
        [
          { name = "Rrbvec push then pop"; run = (fun () -> ignore (Sys.opaque_identity (push_pop_rrbvec config.size))) };
          { name = "BatVect append then pop"; run = (fun () -> ignore (Sys.opaque_identity (push_pop_batvect config.size))) };
        ];
    };
    {
      name = "Concat map";
      cases =
        [
          {
            name = "20k singleton";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (concat_map_singleton concat_map_singleton_input)));
          };
          {
            name = "10k pair";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity (concat_map_pair concat_map_pair_input)));
          };
          {
            name = "20k mostly empty";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (concat_map_mostly_empty concat_map_mostly_empty_input)));
          };
          {
            name = "5k x 33 elements";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (concat_map_constant concat_map_33_values
                        concat_map_chunk_input)));
          };
          {
            name = "200 x 1024 elements";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (concat_map_constant concat_map_1024_values
                        concat_map_1024_input)));
          };
          {
            name = "one large vector";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (concat_map_constant concat_map_large_values
                        concat_map_one_large_input)));
          };
          {
            name = "two large vectors";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (concat_map_constant concat_map_large_values
                        concat_map_two_large_input)));
          };
        ];
    };
    ]
  in
  base_groups @ public_api_benchmark_groups config values @ remaining_groups

let bechamel_name group_name case_name = group_name ^ "/" ^ case_name

let benchmark_config config =
  B.cfg ~limit:config.limit ~quota:(Time.millisecond config.quota_ms) ~kde:None ()

let result_of_ols name raw_results analyzed =
  let estimated_ms, r_square =
    match Hashtbl.find_opt analyzed name with
    | None -> (None, None)
    | Some ols -> (
        match A.OLS.estimates ols with
        | Some [ estimate_ns ] -> (Some (estimate_ns /. 1_000_000.0), A.OLS.r_square ols)
        | _ -> (None, A.OLS.r_square ols))
  in
  let samples =
    match Hashtbl.find_opt raw_results name with
    | None -> None
    | Some result -> Some result.B.stats.samples
  in
  { name; estimated_ms; r_square; samples }

let run_group cfg (group : group) =
  let tests =
    group.cases
    |> List.map (fun (case : case) -> T.make ~name:case.name (S.stage case.run))
    |> T.make_grouped ~name:group.name ~fmt:"%s/%s"
  in
  let instance = Toolkit.Instance.monotonic_clock in
  let analysis = A.ols ~bootstrap:0 ~r_square:true ~predictors:M.[| run |] in
  let raw_results = B.all cfg [ instance ] tests in
  let analyzed = A.all analysis instance raw_results in
  List.map
    (fun (case : case) ->
      let result =
        result_of_ols (bechamel_name group.name case.name) raw_results analyzed
      in
      { result with name = case.name })
    group.cases

let compare_results left right =
  match (left.estimated_ms, right.estimated_ms) with
  | Some left_ms, Some right_ms -> Float.compare left_ms right_ms
  | Some _, None -> -1
  | None, Some _ -> 1
  | None, None -> String.compare left.name right.name

let print_result result =
  match result.estimated_ms with
  | Some estimated_ms ->
      let r_square =
        match result.r_square with
        | None -> "n/a"
        | Some value -> Printf.sprintf "%.4f" value
      in
      let samples =
        match result.samples with
        | None -> "?"
        | Some value -> string_of_int value
      in
      Printf.printf "  %-46s %10.6f ms/run  samples=%s r2=%s\n"
        result.name estimated_ms samples r_square
  | None ->
      Printf.printf "  %-46s %s\n" result.name "analysis unavailable"

let print_group (group : group) results =
  Printf.printf "*%s*\n" group.name;
  results |> List.sort compare_results |> List.iter print_result;
  print_endline ""

let verify config values =
  verify_front_writes config;
  verify_sequential_pops values;
  let read_indices = make_indices config.reads config.size in
  let expected_reads = Array.fold_left ( + ) 0 read_indices in
  check "Rrbvec random read" expected_reads (rrbvec_random_sum values.rrbvec read_indices);
  check "BatVect random read" expected_reads (batvect_random_sum values.batvect read_indices);
  verify_random_write config values (make_indices config.updates config.size);
  verify_map config values;
  verify_conversions config values;
  verify_public_api config values;
  verify_subvec_concat config values;
  verify_push_pop config

let () =
  let config = parse_config () in
  if config.size <= 0 || config.reads < 0 || config.updates < 0 || config.limit <= 0 || config.quota_ms <= 0.0 then
    invalid_arg "benchmark sizes and Bechamel limits must be positive";
  Printf.printf "Benchmark engine: Bechamel\n";
  Printf.printf "size=%d reads=%d updates=%d limit=%d quota-ms=%.3f\n\n"
    config.size config.reads config.updates config.limit config.quota_ms;
  let values = prepare_values config in
  verify config values;
  let cfg = benchmark_config config in
  benchmark_groups config values
  |> List.iter (fun group -> print_group group (run_group cfg group))
