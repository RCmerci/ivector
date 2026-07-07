open Ivector

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

let check_less_or_equal name limit actual =
  if actual > limit then Alcotest.failf "%s: expected <= %d, got %d" name limit actual

let check_raises_invalid_arg name f =
  match f () with
  | exception Invalid_argument _ -> ()
  | exception exn ->
      Alcotest.failf "%s: expected Invalid_argument, got %s" name
        (Printexc.to_string exn)
  | _ -> Alcotest.failf "%s: expected Invalid_argument" name

let check_invariants name v =
  try invariants v
  with exn ->
    Alcotest.failf "%s: invariant failure: %s" name (Printexc.to_string exn)

let range n = List.init n Fun.id

let ceil_log2 n =
  let rec loop power exponent =
    if power >= n then exponent else loop (power lsl 1) (exponent + 1)
  in
  loop 1 0

let append_balance_slack = 8

let append_balance_limit leaves = ceil_log2 leaves + append_balance_slack

let assert_append_balanced name v =
  let rec loop v =
    let record = Obj.repr v in
    let shift = Obj.magic (Obj.field record 1) in
    if shift <> -1 then (0, 1)
    else
      let root = Obj.field record 2 in
      if Obj.is_int root then (0, 1)
      else
        match Obj.tag root with
        | 2 ->
            let left = Obj.magic (Obj.field root 0) in
            let right = Obj.magic (Obj.field root 1) in
            let left_height, left_leaves = loop left in
            let right_height, right_leaves = loop right in
            let height = 1 + max left_height right_height in
            let leaves = left_leaves + right_leaves in
            check_less_or_equal name (append_balance_limit leaves) height;
            (height, leaves)
        | _ -> (0, 1)
  in
  ignore (loop v)

let assert_materialized name v =
  let record = Obj.repr v in
  let shift = Obj.magic (Obj.field record 1) in
  check name (shift <> -1)

let test_empty () =
  let v = empty in
  check_invariants "empty" v;
  check_int "empty length" 0 (length v);
  check "empty is_empty" (is_empty v);
  check_list "empty to_list" [] (to_list v);
  check_raises_invalid_arg "get empty" (fun () -> ignore (get v 0));
  check_raises_invalid_arg "pop empty" (fun () -> ignore (pop v));
  check_raises_invalid_arg "peek empty" (fun () -> ignore (peek v))

let test_invariants_hold_for_public_operations () =
  List.iter
    (fun size ->
      let v = of_list (range size) in
      check_invariants "of_list" v;
      check_invariants "of_array" (of_array (Array.init size Fun.id));
      check_invariants "of_seq" (of_seq (List.to_seq (range size))))
    [ 0; 1; 31; 32; 33; 1024; 1025 ];
  let pushed =
    List.fold_left (fun acc value -> push acc value) empty (range 1100)
  in
  check_invariants "push" pushed;
  check_invariants "set trie" (set pushed 100 42);
  check_invariants "set tail" (set pushed 1099 42);
  check_raises_invalid_arg "set at count" (fun () -> ignore (set pushed 1100 42));
  check_invariants "pop" (pop pushed);
  check_invariants "subvec" (subvec pushed 17 1090);
  let combined =
    concat (subvec pushed 0 500) (subvec pushed 500 (length pushed))
  in
  check_invariants "concat" combined;
  check_invariants "append_list" (append_list pushed [ 1100; 1101 ]);
  check_invariants "append_array" (append_array pushed [| 1100; 1101 |]);
  check_invariants "append_seq" (append_seq pushed (List.to_seq [ 1100; 1101 ]));
  check_invariants "map" (map (( + ) 1) pushed)

let test_push_and_get_across_tail_boundaries () =
  List.iter
    (fun size ->
      let v = of_list (range size) in
      check_int "length after of_list" size (length v);
      check_list "to_list after of_list" (range size) (to_list v);
      for i = 0 to size - 1 do
        check_int "get after of_list" i (get v i)
      done)
    [ 1; 31; 32; 33; 1023; 1024; 1025 ]

let test_persistent_push_keeps_old_vector () =
  let v0 = of_list [ 1; 2; 3 ] in
  let v1 = push v0 4 in
  check_list "old vector after push" [ 1; 2; 3 ] (to_list v0);
  check_list "new vector after push" [ 1; 2; 3; 4 ] (to_list v1)

let test_append_list_preserves_order_across_tail_boundaries () =
  let base = of_list (range 31) in
  let values = List.init 70 (fun i -> i + 31) in
  let appended = append_list base values in
  check_int "append_list length" 101 (length appended);
  check_list "append_list order" (range 101) (to_list appended);
  check_list "append_list keeps original" (range 31) (to_list base)

let test_append_list_empty_list_keeps_values () =
  let v = of_list (range 40) in
  check_list "append_list empty list" (range 40) (to_list (append_list v []))

let test_append_list_large_allocation_is_linear () =
  let size = 100_000 in
  let base = of_array (Array.init 17 Fun.id) in
  let values = List.init size (fun i -> i + 17) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let appended = append_list base values in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "large append_list length" (size + 17) (length appended);
  check_int "large append_list first" 0 (get appended 0);
  check_int "large append_list last" (size + 16) (peek appended);
  check_allocated_less_than "large append_list allocation"
    (float_of_int size *. 120.0)
    allocated

let test_append_array_preserves_order_and_copies_input () =
  let base = of_list (range 31) in
  let values = Array.init 70 (fun i -> i + 31) in
  let appended = append_array base values in
  values.(0) <- -1;
  check_int "append_array length" 101 (length appended);
  check_list "append_array order" (range 101) (to_list appended);
  check_list "append_array keeps original" (range 31) (to_list base)

let test_append_array_empty_array_keeps_values () =
  let v = of_list (range 40) in
  check_list "append_array empty array" (range 40) (to_list (append_array v [||]))

let test_append_seq_consumes_input_once_in_order () =
  let base = of_list (range 31) in
  let next = ref 31 in
  let rec values () =
    if !next = 101 then Seq.Nil
    else
      let value = !next in
      incr next;
      Seq.Cons (value, values)
  in
  let appended = append_seq base values in
  check_int "append_seq consumes input once" 101 !next;
  check_int "append_seq length" 101 (length appended);
  check_list "append_seq order" (range 101) (to_list appended);
  check_list "append_seq keeps original" (range 31) (to_list base)

let test_append_seq_empty_seq_keeps_values () =
  let v = of_list (range 40) in
  check_list "append_seq empty seq" (range 40) (to_list (append_seq v Seq.empty))

let test_set_updates_tail_and_trie_without_mutating_old_vector () =
  let v0 = of_list (range 1050) in
  let v1 = set v0 10 10010 in
  let v2 = set v1 1049 11049 in
  check_int "old trie value preserved" 10 (get v0 10);
  check_int "old tail value preserved" 1049 (get v0 1049);
  check_int "updated trie value" 10010 (get v2 10);
  check_int "updated tail value" 11049 (get v2 1049);
  check_int "intermediate tail value preserved" 1049 (get v1 1049);
  check_int "length after set" 1050 (length v2)

let test_set_at_count_raises_invalid_arg () =
  let v = of_list [ 1; 2; 3 ] in
  check_raises_invalid_arg "set at count" (fun () -> ignore (set v 3 4));
  check_list "set at count keeps old vector" [ 1; 2; 3 ] (to_list v)

let test_pop_and_peek_across_boundaries () =
  let rec drain expected_size v =
    if expected_size = 0 then
      check_raises_invalid_arg "peek drained vector" (fun () -> ignore (peek v))
    else (
      check_int "peek before pop" (expected_size - 1) (peek v);
      let v' = pop v in
      check_int "length after pop" (expected_size - 1) (length v');
      check_list "to_list after pop" (range (expected_size - 1)) (to_list v');
      drain (expected_size - 1) v')
  in
  drain 1050 (of_list (range 1050))

let test_invalid_indices () =
  let v = of_list [ 10; 20; 30 ] in
  check_raises_invalid_arg "negative get" (fun () -> ignore (get v (-1)));
  check_raises_invalid_arg "past end get" (fun () -> ignore (get v 3));
  check_raises_invalid_arg "negative set" (fun () -> ignore (set v (-1) 1));
  check_raises_invalid_arg "past append set" (fun () -> ignore (set v 4 1))

let test_large_roundtrip () =
  let values = range 100_000 in
  let v = of_list values in
  check_int "large length" 100_000 (length v);
  check_int "large first" 0 (get v 0);
  check_int "large middle" 50_000 (get v 50_000);
  check_int "large last" 99_999 (get v 99_999);
  check_list "large roundtrip" values (to_list v)

let test_of_list_large_allocation_uses_array_conversion () =
  let size = 100_000 in
  let values = range size in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let v = of_list values in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "large of_list length" size (length v);
  check_int "large of_list last" (size - 1) (get v (size - 1));
  check "large of_list allocation"
    (allocated < (float_of_int size *. 40.0))

let test_of_array_and_to_array_roundtrip () =
  List.iter
    (fun size ->
      let values = Array.init size Fun.id in
      let v = of_array values in
      check_int "of_array length" size (length v);
      check_array "to_array roundtrip" values (to_array v);
      for i = 0 to size - 1 do
        check_int "get after of_array" i (get v i)
      done)
    [ 0; 1; 31; 32; 33; 1023; 1024; 1025 ]

let test_array_conversions_do_not_share_mutable_storage () =
  let values = [| 1; 2; 3 |] in
  let v = of_array values in
  values.(1) <- 99;
  check_array "of_array copies input" [| 1; 2; 3 |] (to_array v);
  let exported = to_array v in
  exported.(2) <- 77;
  check_int "to_array copies output" 3 (get v 2)

let test_of_array_large_allocation_is_linear_in_array_storage () =
  let size = 100_000 in
  let values = Array.init size Fun.id in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let v = of_array values in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "large of_array length" size (length v);
  check_int "large of_array last" (size - 1) (get v (size - 1));
  check "large of_array allocation"
    (allocated < (float_of_int size *. 80.0))

let test_to_array_large_allocation_avoids_intermediate_list () =
  let size = 100_000 in
  let v = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let values = to_array v in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "large to_array length" size (Array.length values);
  check_int "large to_array last" (size - 1) values.(size - 1);
  check "large to_array allocation"
    (allocated < (float_of_int size *. 16.0))

let test_to_array_supports_subvec_and_concat () =
  let base = of_array (Array.init 80 Fun.id) in
  check_array "subvec to_array"
    (Array.init 53 (fun i -> i + 17))
    (to_array (subvec base 17 70));
  check_array "concat to_array" (Array.init 80 Fun.id)
    (to_array (concat (subvec base 0 40) (subvec base 40 80)))

let test_subvec_returns_materialized_vector () =
  let base = of_array (Array.init 1050 Fun.id) in
  let slice = subvec base 31 1030 in
  assert_materialized "subvec materialized vector" slice;
  check_list "subvec materialized values" (List.init 999 (fun i -> i + 31))
    (to_list slice)

let test_subvec_uses_bulk_array_storage () =
  let size = 100_000 in
  let base = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let slice = subvec base 17 (size - 17) in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "bulk subvec length" (size - 34) (length slice);
  check_int "bulk subvec first" 17 (get slice 0);
  check_int "bulk subvec last" (size - 18) (peek slice);
  check_allocated_less_than "bulk subvec allocation"
    (float_of_int size *. 100.0)
    allocated

let test_of_seq_and_to_seq_roundtrip () =
  List.iter
    (fun size ->
      let values = range size in
      let v = of_seq (List.to_seq values) in
      check_int "of_seq length" size (length v);
      check_list "to_seq roundtrip" values (List.of_seq (to_seq v));
      for i = 0 to size - 1 do
        check_int "get after of_seq" i (get v i)
      done)
    [ 0; 1; 31; 32; 33; 1023; 1024; 1025 ]

let test_of_seq_consumes_input_once_in_order () =
  let next = ref 0 in
  let rec values () =
    if !next = 40 then Seq.Nil
    else
      let value = !next in
      incr next;
      Seq.Cons (value, values)
  in
  let v = of_seq values in
  check_int "of_seq consumes input once" 40 !next;
  check_list "of_seq input order" (range 40) (to_list v)

let test_to_seq_supports_subvec_and_concat () =
  let base = of_array (Array.init 80 Fun.id) in
  check_list "subvec to_seq"
    (List.init 53 (fun i -> i + 17))
    (List.of_seq (to_seq (subvec base 17 70)));
  check_list "concat to_seq" (range 80)
    (List.of_seq (to_seq (concat (subvec base 0 40) (subvec base 40 80))))

let test_fold_left_visits_values_in_order () =
  let v = of_list (range 1050) in
  let visited = fold_left (fun acc value -> value :: acc) [] v |> List.rev in
  check_list "fold_left order" (range 1050) visited;
  check_int "fold_left sum" 550725 (fold_left ( + ) 0 v)

let test_fold_left_empty_keeps_accumulator () =
  let calls = ref 0 in
  let result =
    fold_left
      (fun acc value ->
        incr calls;
        acc + value)
      42 empty
  in
  check_int "fold_left empty accumulator" 42 result;
  check_int "fold_left empty calls" 0 !calls

let test_map_preserves_order_and_length () =
  let v = of_list (range 1050) in
  let mapped = map (fun value -> value * 2) v in
  check_int "map length" 1050 (length mapped);
  check_list "map order" (List.map (fun value -> value * 2) (range 1050)) (to_list mapped)

let test_map_supports_type_changes_and_keeps_original () =
  let v = of_list [ 1; 2; 3 ] in
  let mapped = map string_of_int v in
  check_string_list "map type change" [ "1"; "2"; "3" ] (to_list mapped);
  check_list "map keeps original" [ 1; 2; 3 ] (to_list v)

let test_subvec_extracts_half_open_range () =
  let v = of_list (range 1050) in
  let slice = subvec v 31 1030 in
  check_int "subvec length" 999 (length slice);
  check_list "subvec range" (List.init 999 (fun i -> i + 31)) (to_list slice);
  check_int "subvec fold_left sum" 529470 (fold_left ( + ) 0 slice);
  check_list "subvec whole range" (range 1050) (to_list (subvec v 0 1050));
  check_list "subvec empty range" [] (to_list (subvec v 10 10))

let test_subvec_rejects_invalid_ranges () =
  let v = of_list [ 1; 2; 3 ] in
  check_raises_invalid_arg "subvec negative start" (fun () -> ignore (subvec v (-1) 2));
  check_raises_invalid_arg "subvec inverted range" (fun () -> ignore (subvec v 2 1));
  check_raises_invalid_arg "subvec past end" (fun () -> ignore (subvec v 0 4))

let test_concat_preserves_order_and_operands () =
  let left = of_list (range 1050) in
  let right = of_list (List.init 50 (fun i -> i + 1050)) in
  let combined = concat left right in
  check_int "concat length" 1100 (length combined);
  check_list "concat order" (range 1100) (to_list combined);
  check_list "concat keeps left" (range 1050) (to_list left);
  check_list "concat keeps right" (List.init 50 (fun i -> i + 1050)) (to_list right)

let test_concat_handles_empty_vectors () =
  let v = of_list [ 1; 2; 3 ] in
  check_list "concat empty left" [ 1; 2; 3 ] (to_list (concat empty v));
  check_list "concat empty right" [ 1; 2; 3 ] (to_list (concat v empty));
  check_list "concat empty empty" [] (to_list (concat empty empty))

let test_subvec_and_concat_support_vector_operations () =
  let base = of_list (range 80) in
  let slice = subvec base 17 70 in
  let slice_values = List.init 53 (fun i -> i + 17) in
  check_int "subvec peek" 69 (peek slice);
  check_list "subvec push" (slice_values @ [ 999 ]) (to_list (push slice 999));
  check_list "subvec pop" (List.init 52 (fun i -> i + 17)) (to_list (pop slice));
  check_list
    "subvec set"
    (List.mapi (fun i value -> if i = 20 then 888 else value) slice_values)
    (to_list (set slice 20 888));
  let combined = concat (subvec base 0 40) (subvec base 40 80) in
  check_int "concat peek" 79 (peek combined);
  check_list "concat push" (range 80 @ [ 777 ]) (to_list (push combined 777));
  check_list "concat pop" (range 79) (to_list (pop combined));
  check_list
    "concat set"
    (List.mapi (fun i value -> if i = 45 then 666 else value) (range 80))
    (to_list (set combined 45 666))

let test_deep_concat_traversal_is_stack_safe () =
  let size = 100_000 in
  let combined =
    let rec loop i acc =
      if i = size then acc else loop (i + 1) (concat acc (of_list [ i ]))
    in
    loop 0 empty
  in
  check_int "deep concat length" size (length combined);
  check_int "deep concat fold_left sum" 4_999_950_000
    (fold_left ( + ) 0 combined);
  check_int "deep concat to_list head" 0 (List.hd (to_list combined))

let test_deep_concat_to_array_is_stack_safe () =
  let size = 100_000 in
  let combined =
    let rec loop i acc =
      if i = size then acc else loop (i + 1) (concat acc (of_list [ i ]))
    in
    loop 0 empty
  in
  let values = to_array combined in
  check_int "deep concat to_array length" size (Array.length values);
  check_int "deep concat to_array head" 0 values.(0);
  check_int "deep concat to_array last" (size - 1) values.(size - 1)

let test_left_associated_concat_stays_balanced () =
  let size = 10_000 in
  let combined =
    let rec loop i acc =
      if i = size then acc else loop (i + 1) (concat acc (of_list [ i ]))
    in
    loop 0 empty
  in
  assert_append_balanced "left-associated concat append balance" combined;
  check_int "left-associated concat length" size (length combined);
  check_int "left-associated concat first" 0 (get combined 0);
  check_int "left-associated concat middle" (size / 2) (get combined (size / 2));
  check_int "left-associated concat last" (size - 1) (peek combined);
  check_list "left-associated concat order" (range size) (to_list combined)

let test_right_associated_concat_stays_balanced () =
  let size = 10_000 in
  let combined =
    let rec loop i acc =
      if i < 0 then acc else loop (i - 1) (concat (of_list [ i ]) acc)
    in
    loop (size - 1) empty
  in
  assert_append_balanced "right-associated concat append balance" combined;
  check_int "right-associated concat length" size (length combined);
  check_int "right-associated concat first" 0 (get combined 0);
  check_int "right-associated concat middle" (size / 2) (get combined (size / 2));
  check_int "right-associated concat last" (size - 1) (peek combined);
  check_list "right-associated concat order" (range size) (to_list combined)

let test_mixed_subvec_concat_stays_balanced () =
  let base = of_array (Array.init 12_000 Fun.id) in
  let combined =
    let rec loop i acc =
      if i = 120 then acc
      else
        let start = i * 50 in
        let chunk = subvec base start (start + 50) in
        loop (i + 1) (concat acc chunk)
    in
    loop 0 empty
  in
  let expected = List.init 6_000 Fun.id in
  assert_append_balanced "mixed subvec concat append balance" combined;
  check_int "mixed subvec concat length" 6_000 (length combined);
  check_list "mixed subvec concat order" expected (to_list combined);
  check_list "mixed subvec concat push"
    (expected @ [ 42_000 ])
    (to_list (push combined 42_000));
  check_list "mixed subvec concat pop"
    (List.init 5_999 Fun.id)
    (to_list (pop combined));
  check_list "mixed subvec concat set"
    (List.mapi (fun i value -> if i = 2_000 then -1 else value) expected)
    (to_list (set combined 2_000 (-1)))

let test_case name test =
  Alcotest.test_case name `Quick test

let allocation_test_case name test =
  Alcotest.test_case name `Slow test

let () =
  Alcotest.run "ivector"
    [
      ( "core",
        [
          test_case "empty" test_empty;
          test_case "invariants_hold_for_public_operations"
            test_invariants_hold_for_public_operations;
          test_case "push_and_get_across_tail_boundaries"
            test_push_and_get_across_tail_boundaries;
          test_case "persistent_push_keeps_old_vector"
            test_persistent_push_keeps_old_vector;
          test_case "set_updates_tail_and_trie_without_mutating_old_vector"
            test_set_updates_tail_and_trie_without_mutating_old_vector;
          test_case "set_at_count_raises_invalid_arg"
            test_set_at_count_raises_invalid_arg;
          test_case "pop_and_peek_across_boundaries"
            test_pop_and_peek_across_boundaries;
          test_case "invalid_indices" test_invalid_indices;
          allocation_test_case "large_roundtrip" test_large_roundtrip;
        ] );
      ( "append",
        [
          test_case "append_list_preserves_order_across_tail_boundaries"
            test_append_list_preserves_order_across_tail_boundaries;
          test_case "append_list_empty_list_keeps_values"
            test_append_list_empty_list_keeps_values;
          allocation_test_case "append_list_large_allocation_is_linear"
            test_append_list_large_allocation_is_linear;
          test_case "append_array_preserves_order_and_copies_input"
            test_append_array_preserves_order_and_copies_input;
          test_case "append_array_empty_array_keeps_values"
            test_append_array_empty_array_keeps_values;
          test_case "append_seq_consumes_input_once_in_order"
            test_append_seq_consumes_input_once_in_order;
          test_case "append_seq_empty_seq_keeps_values"
            test_append_seq_empty_seq_keeps_values;
        ] );
      ( "conversion",
        [
          allocation_test_case "of_list_large_allocation_uses_array_conversion"
            test_of_list_large_allocation_uses_array_conversion;
          test_case "of_array_and_to_array_roundtrip"
            test_of_array_and_to_array_roundtrip;
          test_case "array_conversions_do_not_share_mutable_storage"
            test_array_conversions_do_not_share_mutable_storage;
          allocation_test_case "of_array_large_allocation_is_linear_in_array_storage"
            test_of_array_large_allocation_is_linear_in_array_storage;
          allocation_test_case "to_array_large_allocation_avoids_intermediate_list"
            test_to_array_large_allocation_avoids_intermediate_list;
          test_case "to_array_supports_subvec_and_concat"
            test_to_array_supports_subvec_and_concat;
          test_case "of_seq_and_to_seq_roundtrip" test_of_seq_and_to_seq_roundtrip;
          test_case "of_seq_consumes_input_once_in_order"
            test_of_seq_consumes_input_once_in_order;
          test_case "to_seq_supports_subvec_and_concat"
            test_to_seq_supports_subvec_and_concat;
        ] );
      ( "transform",
        [
          test_case "fold_left_visits_values_in_order"
            test_fold_left_visits_values_in_order;
          test_case "fold_left_empty_keeps_accumulator"
            test_fold_left_empty_keeps_accumulator;
          test_case "map_preserves_order_and_length"
            test_map_preserves_order_and_length;
          test_case "map_supports_type_changes_and_keeps_original"
            test_map_supports_type_changes_and_keeps_original;
        ] );
      ( "subvec",
        [
          test_case "subvec_returns_materialized_vector"
            test_subvec_returns_materialized_vector;
          allocation_test_case "subvec_uses_bulk_array_storage"
            test_subvec_uses_bulk_array_storage;
          test_case "subvec_extracts_half_open_range"
            test_subvec_extracts_half_open_range;
          test_case "subvec_rejects_invalid_ranges" test_subvec_rejects_invalid_ranges;
        ] );
      ( "concat",
        [
          test_case "concat_preserves_order_and_operands"
            test_concat_preserves_order_and_operands;
          test_case "concat_handles_empty_vectors" test_concat_handles_empty_vectors;
          test_case "subvec_and_concat_support_vector_operations"
            test_subvec_and_concat_support_vector_operations;
          allocation_test_case "deep_concat_traversal_is_stack_safe"
            test_deep_concat_traversal_is_stack_safe;
          allocation_test_case "deep_concat_to_array_is_stack_safe"
            test_deep_concat_to_array_is_stack_safe;
          allocation_test_case "left_associated_concat_stays_balanced"
            test_left_associated_concat_stays_balanced;
          allocation_test_case "right_associated_concat_stays_balanced"
            test_right_associated_concat_stays_balanced;
          test_case "mixed_subvec_concat_stays_balanced"
            test_mixed_subvec_concat_stays_balanced;
        ] );
    ]
