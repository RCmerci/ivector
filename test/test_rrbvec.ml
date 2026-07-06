open Rrbvec

let check name condition =
  Alcotest.(check bool) name true condition

let check_int name expected actual =
  Alcotest.(check int) name expected actual

let check_list name expected actual =
  Alcotest.(check (list int)) name expected actual

let check_string_list name expected actual =
  Alcotest.(check (list string)) name expected actual

let check_array name expected actual =
  Alcotest.(check (array int)) name expected actual

let check_allocated_less_than name limit actual =
  if not (actual < limit) then
    Alcotest.failf "%s: expected < %.0f bytes, got %.0f bytes" name limit
      actual

let check_raises_invalid_arg name f =
  match f () with
  | exception Invalid_argument _ -> ()
  | exception exn ->
      Alcotest.failf "%s: expected Invalid_argument, got %s" name
        (Printexc.to_string exn)
  | _ -> Alcotest.failf "%s: expected Invalid_argument" name

let string_contains ~needle haystack =
  let needle_length = String.length needle in
  let haystack_length = String.length haystack in
  let rec loop index =
    index + needle_length <= haystack_length
    && (String.sub haystack index needle_length = needle || loop (index + 1))
  in
  needle_length = 0 || loop 0

let check_invariants name v =
  try invariants v
  with exn ->
    Alcotest.failf "%s: invariant failure: %s" name (Printexc.to_string exn)

let check_invariant_failure_contains name expected_message v =
  match invariants v with
  | () -> Alcotest.failf "%s: expected invariant failure" name
  | exception exn ->
      let message = Printexc.to_string exn in
      if not (string_contains ~needle:expected_message message) then
        Alcotest.failf "%s: expected invariant failure containing %S, got %s" name
          expected_message message

let range n = List.init n Fun.id

let list_slice values start stop =
  let rec drop count values =
    if count = 0 then values
    else
      match values with
      | [] -> []
      | _ :: rest -> drop (count - 1) rest
  in
  let rec take count values acc =
    if count = 0 then List.rev acc
    else
      match values with
      | [] -> invalid_arg "not enough values"
      | value :: rest -> take (count - 1) rest (value :: acc)
  in
  take (stop - start) (drop start values) []

let rrb_width = 32

let internal_height v =
  let root = Obj.field (Obj.repr v) 1 in
  if Obj.is_int root then -1
  else
    match Obj.tag root with
    | 0 -> 0
    | 1 -> (Obj.magic (Obj.field root 3) : int)
    | _ -> Alcotest.fail "unexpected rrb node tag"

type 'a raw_node =
  | Raw_empty
  | Raw_leaf of 'a array
  | Raw_branch of {
      children : 'a raw_node array;
      sizes : int array;
      count : int;
      height : int;
      leaves : int;
    }

type 'a raw_vector = {
  count : int;
  root : 'a raw_node;
  tail : 'a array;
  tailoff : int;
  head : 'a array;
}

let unsafe_vector raw = (Obj.magic raw : int t)

let raw_leaf length = Raw_leaf (Array.init length Fun.id)

let raw_branch children =
  let sizes = Array.make (Array.length children) 0 in
  let count = ref 0 in
  let height = ref (-1) in
  let leaves = ref 0 in
  Array.iteri
    (fun index child ->
      let child_count, child_height, child_leaves =
        match child with
        | Raw_empty -> (0, -1, 0)
        | Raw_leaf values -> (Array.length values, 0, 1)
        | Raw_branch branch -> (branch.count, branch.height, branch.leaves)
      in
      count := !count + child_count;
      height := max !height child_height;
      leaves := !leaves + child_leaves;
      Array.unsafe_set sizes index !count)
    children;
  Raw_branch
    {
      children;
      sizes;
      count = !count;
      height = !height + 1;
      leaves = !leaves;
    }

let raw_vector root =
  let count =
    match root with
    | Raw_empty -> 0
    | Raw_leaf values -> Array.length values
    | Raw_branch branch -> branch.count
  in
  unsafe_vector
    {
      count;
      root;
      tail = [||];
      tailoff = count;
      head = [||];
    }

let test_empty () =
  let v = empty in
  check_invariants "empty" v;
  check_int "empty length" 0 (length v);
  check "empty is_empty" (is_empty v);
  check_list "empty to_list" [] (to_list v);
  check_raises_invalid_arg "get empty" (fun () -> ignore (get v 0));
  check_raises_invalid_arg "pop empty" (fun () -> ignore (pop_back v));
  check_raises_invalid_arg "peek empty" (fun () -> ignore (peek_back v))

let test_invariants_hold_for_public_operations () =
  List.iter
    (fun size ->
      let values = range size in
      check_invariants "of_list" (of_list values);
      check_invariants "of_array" (of_array (Array.init size Fun.id));
      check_invariants "of_seq" (of_seq (List.to_seq values)))
    [ 0; 1; 31; 32; 33; 1024; 1025 ];
  List.iter
    (fun size ->
      let pushed =
        List.fold_left (fun acc value -> push_back acc value) empty (range size)
      in
      check_invariants "push boundary" pushed)
    [ 1057; 1088; 1089 ];
  let pushed =
    List.fold_left (fun acc value -> push_back acc value) empty (range 1100)
  in
  check_invariants "push" pushed;
  check_invariants "set trie" (set pushed 100 42);
  check_invariants "set append" (set pushed 1100 42);
  check_invariants "pop" (snd (pop_back pushed));
  check_invariants "subvec" (subvec pushed 17 1090);
  let combined =
    concat (subvec pushed 0 500) (subvec pushed 500 (length pushed))
  in
  check_invariants "concat" combined;
  check_invariants "append_list" (append_list pushed [ 1100; 1101 ]);
  check_invariants "append_array" (append_array pushed [| 1100; 1101 |]);
  check_invariants "of_seq" (of_seq (List.to_seq [ 1100; 1101 ]));
  check_invariants "map" (map (( + ) 1) pushed)

let test_invariants_report_malformed_leaf () =
  let malformed =
    raw_vector
      (Raw_branch
         {
           children = [| raw_leaf 0; raw_leaf 1 |];
           sizes = [| 0; 1 |];
           count = 1;
           height = 1;
           leaves = 2;
         })
  in
  check_invariant_failure_contains "empty leaf" "leaf length must be positive"
    malformed

let test_invariants_reject_root_singleton_branch () =
  let malformed = raw_vector (raw_branch [| raw_leaf rrb_width |]) in
  check_invariant_failure_contains "root singleton branch"
    "root branch must have more than one child" malformed

let test_invariants_reject_child_height_mismatch () =
  let taller_child = raw_branch [| raw_leaf 1; raw_leaf 1 |] in
  let malformed =
    unsafe_vector
      {
        count = 3;
        root =
          Raw_branch
            {
              children = [| raw_leaf 1; taller_child |];
              sizes = [| 1; 3 |];
              count = 3;
              height = 2;
              leaves = 3;
            };
        tail = [||];
        tailoff = 3;
        head = [||];
      }
  in
  check_invariant_failure_contains "child height mismatch"
    "child height must equal branch height - 1" malformed

let test_invariants_reject_skinny_search_step () =
  let malformed =
    raw_vector (raw_branch (Array.init rrb_width (fun _ -> raw_leaf 1)))
  in
  check_invariant_failure_contains "skinny search step" "relaxed search step"
    malformed

let test_invariants_reject_linear_height_degradation () =
  let rec skinny_chain height =
    if height = 0 then raw_leaf 1
    else
      Raw_branch
        {
          children = [| skinny_chain (height - 1) |];
          sizes = [| 1 |];
          count = 1;
          height;
          leaves = 1;
        }
  in
  let root_height = 10 in
  let malformed =
    unsafe_vector
      {
        count = 2;
        root =
          Raw_branch
            {
              children =
                [| skinny_chain (root_height - 1); skinny_chain (root_height - 1) |];
              sizes = [| 1; 2 |];
              count = 2;
              height = root_height;
              leaves = 2;
            };
        tail = [||];
        tailoff = 2;
        head = [||];
      }
  in
  check_invariant_failure_contains "height bound" "height bound" malformed

let test_push_get_and_persistence () =
  List.iter
    (fun size ->
      let v = of_list (range size) in
      check_invariants "of_list vector" v;
      check_int "length" size (length v);
      check_list "to_list" (range size) (to_list v);
      for i = 0 to size - 1 do
        check_int "get" i (get v i)
      done)
    [ 1; 31; 32; 33; 1023; 1024; 1025 ];
  let v0 = of_list [ 1; 2; 3 ] in
  let v1 = push_back v0 4 in
  check_list "old vector after push" [ 1; 2; 3 ] (to_list v0);
  check_list "new vector after push" [ 1; 2; 3; 4 ] (to_list v1)

let test_set_pop_and_peek () =
  let v0 = of_list (range 1050) in
  let v1 = set v0 10 10010 in
  let v2 = set v1 1049 11049 in
  let v3 = set v2 1050 21050 in
  check_invariants "set append" v3;
  check_int "old value preserved" 10 (get v0 10);
  check_int "updated trie value" 10010 (get v3 10);
  check_int "updated last value" 11049 (get v3 1049);
  check_int "set at count appends" 21050 (peek_back v3);
  check_list "pop removes last" (to_list v2) (to_list (snd (pop_back v3)));
  check_raises_invalid_arg "negative set" (fun () -> ignore (set v0 (-1) 1));
  check_raises_invalid_arg "past append set" (fun () -> ignore (set v0 1051 1))

let test_front_and_back_operations () =
  let v0 = of_list [ 2; 3 ] in
  let v1 = push_front v0 1 |> fun v -> push_back v 4 in
  check_invariants "push_front/push_back" v1;
  check_list "front/back push order" [ 1; 2; 3; 4 ] (to_list v1);
  check_int "peek_front" 1 (peek_front v1);
  check_int "peek_back" 4 (peek_back v1);
  let front, v2 = pop_front v1 in
  let back, v3 = pop_back v2 in
  check_int "pop_front value" 1 front;
  check_int "pop_back value" 4 back;
  check_list "pop front/back vector" [ 2; 3 ] (to_list v3);
  check_list "append alias" [ 1; 2; 3; 4 ]
    (to_list (append (of_list [ 1; 2 ]) (of_list [ 3; 4 ])));
  check_list "prepend alias" [ 1; 2; 3; 4 ]
    (to_list (prepend (of_list [ 1; 2 ]) (of_list [ 3; 4 ])));
  check_list "prepend_list" [ 1; 2; 3; 4 ]
    (to_list (prepend_list (of_list [ 3; 4 ]) [ 1; 2 ]));
  check_list "prepend_arrat" [ 1; 2; 3; 4 ]
    (to_list (prepend_arrat (of_list [ 3; 4 ]) [| 1; 2 |]));
  check_raises_invalid_arg "pop_front empty" (fun () -> ignore (pop_front empty));
  check_raises_invalid_arg "pop_back empty" (fun () -> ignore (pop_back empty));
  check_raises_invalid_arg "peek_front empty" (fun () -> ignore (peek_front empty));
  check_raises_invalid_arg "peek_back empty" (fun () -> ignore (peek_back empty))

let test_concat_and_subvec_preserve_order () =
  let left = of_list (range 1050) in
  let right = of_list (List.init 70 (fun i -> i + 1050)) in
  let combined = concat left right in
  check_invariants "concat" combined;
  check_int "concat length" 1120 (length combined);
  check_list "concat order" (range 1120) (to_list combined);
  check_list "concat keeps left" (range 1050) (to_list left);
  check_list "concat keeps right" (List.init 70 (fun i -> i + 1050)) (to_list right);
  let slice = subvec combined 31 1090 in
  check_invariants "subvec" slice;
  check_int "subvec length" 1059 (length slice);
  check_list "subvec order" (List.init 1059 (fun i -> i + 31)) (to_list slice);
  check_list "empty subvec" [] (to_list (subvec combined 10 10));
  check_raises_invalid_arg "subvec negative start" (fun () ->
      ignore (subvec combined (-1) 2));
  check_raises_invalid_arg "subvec inverted range" (fun () ->
      ignore (subvec combined 2 1));
  check_raises_invalid_arg "subvec past end" (fun () ->
      ignore (subvec combined 0 1121))

let test_subvec_slices_head_root_and_tail () =
  let root_values = range 2048 in
  let tail_values = List.init 15 (fun i -> i + 2048) in
  let head_values = List.init 10 (fun i -> i - 10) in
  let base = of_list root_values in
  let with_tail = List.fold_left push_back base tail_values in
  let values =
    List.fold_right (fun value acc -> push_front acc value) head_values with_tail
  in
  let expected = head_values @ root_values @ tail_values in
  let cases =
    [
      ("inside head", 2, 8);
      ("head into root", 5, 20);
      ("inside root leaf", 41, 45);
      ("across root children", 110, 1900);
      ("root into tail", 2055, 2068);
      ("inside tail", 2060, 2073);
      ("whole vector", 0, length values);
    ]
  in
  List.iter
    (fun (name, start, stop) ->
      let slice = subvec values start stop in
      check_invariants ("subvec " ^ name) slice;
      check_int (name ^ " length") (stop - start) (length slice);
      check_list (name ^ " order") (list_slice expected start stop)
        (to_list slice))
    cases

let test_subvec_small_slice_allocation_does_not_scale_with_vector_length () =
  let size = 100_000 in
  let values = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let slice = subvec values 50_000 50_010 in
  let allocated = Gc.allocated_bytes () -. before in
  check_invariants "small subvec allocation" slice;
  check_int "small subvec allocation length" 10 (length slice);
  check_list "small subvec allocation order" (List.init 10 (fun i -> i + 50_000))
    (to_list slice);
  check_allocated_less_than "small subvec allocation" 200_000. allocated

let test_subvec_collapses_promoted_singleton_root () =
  let promoted =
    concat (of_list [ 0 ]) (of_array (Array.init 1024 (fun i -> i + 1)))
  in
  check_invariants "promoted concat" promoted;
  let slice = subvec promoted 0 1 in
  check_invariants "singleton root subvec" slice;
  check_list "singleton root subvec order" [ 0 ] (to_list slice)

let test_concat_keeps_child_heights_uniform () =
  let combined = concat (of_array (Array.init 1024 Fun.id)) (of_list [ 1024 ]) in
  check_invariants "concat uniform child heights" combined;
  check_int "concat uniform length" 1025 (length combined);
  check_list "concat uniform order" (range 1025) (to_list combined)

let test_repeated_concat_stays_stack_safe () =
  let size = 20_000 in
  let combined =
    let rec loop i acc =
      if i = size then acc else loop (i + 1) (concat acc (of_list [ i ]))
    in
    loop 0 empty
  in
  check_invariants "deep concat" combined;
  check_int "deep concat length" size (length combined);
  check_int "deep concat first" 0 (get combined 0);
  check_int "deep concat middle" (size / 2) (get combined (size / 2));
  check_int "deep concat last" (size - 1) (peek_back combined);
  check_int "deep concat sum" ((size * (size - 1)) / 2) (fold_left ( + ) 0 combined)

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

let test_repeated_chunk_concat_satisfies_relaxed_density () =
  let size = 50_000 in
  let values = of_array (Array.init size Fun.id) in
  let chunks =
    List.map
      (fun (start, length) -> subvec values start (start + length))
      (chunk_bounds size 8)
  in
  let combined =
    match chunks with
    | [] -> Alcotest.fail "expected chunks"
    | first :: rest -> List.fold_left concat first rest
  in
  check_invariants "repeated chunk concat" combined;
  check_int "repeated chunk concat length" size (length combined);
  check_int "repeated chunk concat first" 0 (get combined 0);
  check_int "repeated chunk concat last" (size - 1) (peek_back combined);
  check_int "repeated chunk concat sum" ((size * (size - 1)) / 2)
    (fold_left ( + ) 0 combined)

let test_push_large_allocation_is_linear () =
  let size = 20_000 in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let values =
    let rec loop i acc =
      if i = size then acc else loop (i + 1) (push_back acc i)
    in
    loop 0 empty
  in
  let allocated = Gc.allocated_bytes () -. before in
  check_invariants "large push allocation" values;
  check_int "large push length" size (length values);
  check_int "large push last" (size - 1) (peek_back values);
  check_allocated_less_than "large push allocation" 60_000_000. allocated

let test_push_keeps_height_logarithmic () =
  let size = 20_000 in
  let values =
    let rec loop i acc =
      if i = size then acc else loop (i + 1) (push_back acc i)
    in
    loop 0 empty
  in
  check_invariants "large push height" values;
  check_int "large push logarithmic height" 2 (internal_height values)

let test_push_front_large_allocation_is_linear () =
  let size = 20_000 in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let values =
    let rec loop i acc =
      if i = size then acc else loop (i + 1) (push_front acc i)
    in
    loop 0 empty
  in
  let allocated = Gc.allocated_bytes () -. before in
  check_invariants "large push_front allocation" values;
  check_int "large push_front length" size (length values);
  check_int "large push_front first" (size - 1) (peek_front values);
  check_int "large push_front last" 0 (peek_back values);
  check_allocated_less_than "large push_front allocation" 60_000_000. allocated

let test_fold_right_visits_values_in_order () =
  let v = append (of_list (range 1050)) (of_list (List.init 70 (fun i -> i + 1050))) in
  check_list "fold_right order" (range 1120) (fold_right (fun value acc -> value :: acc) v []);
  check_int "fold_right sum" 626640 (fold_right ( + ) v 0);
  check_string_list "fold_right type change" [ "1"; "2"; "3" ]
    (fold_right (fun value acc -> string_of_int value :: acc) (of_list [ 1; 2; 3 ]) [])

let test_fold_right_large_allocation_is_linear () =
  let size = 100_000 in
  let v = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let sum = fold_right ( + ) v 0 in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "large fold_right sum" ((size * (size - 1)) / 2) sum;
  check_allocated_less_than "large fold_right allocation" 5_000_000. allocated

let test_conversions_and_map () =
  let values = [| 1; 2; 3 |] in
  let v = of_array values in
  values.(1) <- 99;
  check_array "of_array copies input" [| 1; 2; 3 |] (to_array v);
  let exported = to_array v in
  exported.(2) <- 77;
  check_int "to_array copies output" 3 (get v 2);
  let mapped = map string_of_int v in
  check_string_list "map type change" [ "1"; "2"; "3" ] (to_list mapped);
  check_list "of_seq/to_seq" (range 40) (List.of_seq (to_seq (of_seq (List.to_seq (range 40)))));
  check_list "append_list" (range 70) (to_list (append_list (of_list (range 31)) (List.init 39 (fun i -> i + 31))));
  check_list "append_array" (range 70) (to_list (append_array (of_list (range 31)) (Array.init 39 (fun i -> i + 31))));
  check_list "of_seq" (range 70)
    (to_list (of_seq (List.to_seq (range 70))))

let test_case name test =
  Alcotest.test_case name `Quick test

let () =
  Alcotest.run "rrbvec"
    [
      ( "core",
        [
          test_case "empty" test_empty;
          test_case "invariants_hold_for_public_operations"
            test_invariants_hold_for_public_operations;
          test_case "invariants_report_malformed_leaf"
            test_invariants_report_malformed_leaf;
          test_case "invariants_reject_root_singleton_branch"
            test_invariants_reject_root_singleton_branch;
          test_case "invariants_reject_child_height_mismatch"
            test_invariants_reject_child_height_mismatch;
          test_case "invariants_reject_skinny_search_step"
            test_invariants_reject_skinny_search_step;
          test_case "invariants_reject_linear_height_degradation"
            test_invariants_reject_linear_height_degradation;
          test_case "push_get_and_persistence" test_push_get_and_persistence;
          test_case "set_pop_and_peek" test_set_pop_and_peek;
          test_case "front_and_back_operations" test_front_and_back_operations;
        ] );
      ( "rrb",
        [
          test_case "concat_and_subvec_preserve_order"
            test_concat_and_subvec_preserve_order;
          test_case "subvec_slices_head_root_and_tail"
            test_subvec_slices_head_root_and_tail;
          test_case "subvec_small_slice_allocation_does_not_scale_with_vector_length"
            test_subvec_small_slice_allocation_does_not_scale_with_vector_length;
          test_case "subvec_collapses_promoted_singleton_root"
            test_subvec_collapses_promoted_singleton_root;
          test_case "concat_keeps_child_heights_uniform"
            test_concat_keeps_child_heights_uniform;
          test_case "repeated_concat_stays_stack_safe"
            test_repeated_concat_stays_stack_safe;
          test_case "repeated_chunk_concat_satisfies_relaxed_density"
            test_repeated_chunk_concat_satisfies_relaxed_density;
          test_case "push_large_allocation_is_linear"
            test_push_large_allocation_is_linear;
          test_case "push_keeps_height_logarithmic"
            test_push_keeps_height_logarithmic;
          test_case "push_front_large_allocation_is_linear"
            test_push_front_large_allocation_is_linear;
        ] );
      ( "conversion",
        [
          test_case "conversions_and_map" test_conversions_and_map;
          test_case "fold_right_visits_values_in_order"
            test_fold_right_visits_values_in_order;
          test_case "fold_right_large_allocation_is_linear"
            test_fold_right_large_allocation_is_linear;
        ] );
    ]
