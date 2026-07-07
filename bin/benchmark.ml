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
    "ivector-bench [--size N] [--reads N] [--updates N] [--limit N] [--quota-ms N]";
  { size = !size; reads = !reads; updates = !updates; limit = !limit; quota_ms = !quota_ms }

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

let push_pop_rrbvec size =
  let rec push_loop i values =
    if i = size then values else push_loop (i + 1) (Rrbvec.push_back values i)
  in
  let rec pop_loop values =
    if Rrbvec.is_empty values then values else pop_loop (snd (Rrbvec.pop_back values))
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

let verify_random_write config values indices =
  let expected = expected_update_sum config.size indices in
  let rrbvec_updated = update_rrbvec values.rrbvec indices in
  let batvect_updated = update_batvect values.batvect indices in
  check_rrbvec_invariants "Rrbvec random write (set)" rrbvec_updated;
  check "Rrbvec random write (set)" expected (sum_rrbvec rrbvec_updated);
  check "BatVect random write (set)" expected (sum_batvect batvect_updated)

let verify_subvec_concat config values =
  let subvec_steps = min 8 ((config.size - 1) / 2) in
  let final_length = config.size - (2 * subvec_steps) in
  let expected_subvec_sum = range_sum subvec_steps final_length in
  let rrbvec_subvec = repeated_rrbvec_subvec subvec_steps values.rrbvec in
  check_rrbvec_invariants "Rrbvec repeated subvec" rrbvec_subvec;
  check "Rrbvec repeated subvec length" final_length (Rrbvec.length rrbvec_subvec);
  check "Rrbvec repeated subvec sum" expected_subvec_sum (sum_rrbvec rrbvec_subvec);
  let batvect_subvec = repeated_batvect_subvec subvec_steps values.batvect in
  check "BatVect repeated subvec length" final_length (BatVect.length batvect_subvec);
  check "BatVect repeated subvec sum" expected_subvec_sum (sum_batvect batvect_subvec);
  let chunks = min 8 config.size in
  let bounds = chunk_bounds config.size chunks in
  let expected_concat_sum = range_sum 0 config.size in
  let rrbvec_concat =
    bounds
    |> List.map (fun (start, length) -> Rrbvec.subvec values.rrbvec start (start + length))
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

let benchmark_groups config values =
  let read_indices = make_indices config.reads config.size in
  let update_indices = make_indices config.updates config.size in
  let subvec_steps = min 8 ((config.size - 1) / 2) in
  let bounds = chunk_bounds config.size (min 8 config.size) in
  [
    {
      name = "Sequential write";
      cases =
        [
          { name = "Rrbvec sequential write (push_back)"; run = (fun () -> ignore (Sys.opaque_identity (build_rrbvec config.size))) };
          { name = "BatVect sequential write (append)"; run = (fun () -> ignore (Sys.opaque_identity (build_batvect config.size))) };
          { name = "Rrbvec sequential write (push_front)"; run = (fun () -> ignore (Sys.opaque_identity (build_rrbvec_front config.size))) };
          { name = "BatVect sequential write (push_front)"; run = (fun () -> ignore (Sys.opaque_identity (build_batvect_front config.size))) };
        ];
    };
    {
      name = "Sequential read";
      cases =
        [
          { name = "Rrbvec sequential read (fold_left)"; run = (fun () -> ignore (Sys.opaque_identity (sum_rrbvec values.rrbvec))) };
          { name = "Rrbvec sequential read (fold_right)"; run = (fun () -> ignore (Sys.opaque_identity (Rrbvec.fold_right ( + ) values.rrbvec 0))) };
          { name = "BatVect sequential read (fold_left)"; run = (fun () -> ignore (Sys.opaque_identity (sum_batvect values.batvect))) };
          { name = "BatVect sequential read (fold_right)"; run = (fun () -> ignore (Sys.opaque_identity (BatVect.fold_right ( + ) values.batvect 0))) };
        ];
    };
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
          { name = "Rrbvec repeated subvec"; run = (fun () -> ignore (Sys.opaque_identity (repeated_rrbvec_subvec subvec_steps values.rrbvec))) };
          { name = "BatVect repeated subvec"; run = (fun () -> ignore (Sys.opaque_identity (repeated_batvect_subvec subvec_steps values.batvect))) };
          {
            name = "Rrbvec repeated concat";
            run =
              (fun () ->
                ignore
                  (Sys.opaque_identity
                     (bounds
                     |> List.map (fun (start, length) -> Rrbvec.subvec values.rrbvec start (start + length))
                     |> concat_nonempty Rrbvec.concat)));
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
  ]

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
  let read_indices = make_indices config.reads config.size in
  let expected_reads = Array.fold_left ( + ) 0 read_indices in
  check "Rrbvec random read" expected_reads (rrbvec_random_sum values.rrbvec read_indices);
  check "BatVect random read" expected_reads (batvect_random_sum values.batvect read_indices);
  verify_random_write config values (make_indices config.updates config.size);
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
