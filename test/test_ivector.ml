open Ivector

let check name condition =
  if not condition then failwith name

let check_int name expected actual =
  if expected <> actual then
    failwith (Printf.sprintf "%s: expected %d, got %d" name expected actual)

let check_list name expected actual =
  if expected <> actual then failwith name

let check_array name expected actual =
  if expected <> actual then
    failwith
      (Printf.sprintf "%s: expected [%s], got [%s]" name
         (String.concat "; "
            (Array.to_list (Array.map string_of_int expected)))
         (String.concat "; " (Array.to_list (Array.map string_of_int actual))))

let check_allocated_less_than name limit actual =
  if not (actual < limit) then
    failwith
      (Printf.sprintf "%s: expected < %.0f bytes, got %.0f bytes" name limit
         actual)

let check_raises_invalid_arg name f =
  match f () with
  | exception Invalid_argument _ -> ()
  | exception exn ->
      failwith
        (Printf.sprintf "%s: expected Invalid_argument, got %s" name
           (Printexc.to_string exn))
  | _ -> failwith (name ^ ": expected Invalid_argument")

let range n = List.init n Fun.id

let test_empty () =
  let v = empty in
  check_int "empty length" 0 (length v);
  check "empty is_empty" (is_empty v);
  check_list "empty to_list" [] (to_list v);
  check_raises_invalid_arg "get empty" (fun () -> ignore (get v 0));
  check_raises_invalid_arg "pop empty" (fun () -> ignore (pop v));
  check_raises_invalid_arg "peek empty" (fun () -> ignore (peek v))

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

let test_set_at_count_appends_like_clojure_assocn () =
  let v = of_list [ 1; 2; 3 ] in
  let appended = set v 3 4 in
  check_list "set at count appends" [ 1; 2; 3; 4 ] (to_list appended);
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

let test_to_array_supports_views () =
  let base = of_array (Array.init 80 Fun.id) in
  check_array "subvec to_array"
    (Array.init 53 (fun i -> i + 17))
    (to_array (subvec base 17 70));
  check_array "concat to_array" (Array.init 80 Fun.id)
    (to_array (concat (subvec base 0 40) (subvec base 40 80)))

let test_materializing_view_for_push_uses_linear_array_storage () =
  let size = 100_000 in
  let view = subvec (of_array (Array.init size Fun.id)) 0 size in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let pushed = push view (-1) in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "materialized view push length" (size + 1) (length pushed);
  check_int "materialized view push last" (-1) (peek pushed);
  check_allocated_less_than "materialized view push allocation"
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

let test_to_seq_supports_views () =
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
  check_list "map type change" [ "1"; "2"; "3" ] (to_list mapped);
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

let test_views_support_vector_operations () =
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

let () =
  List.iter
    (fun (name, test) ->
      try test () with
      | exn ->
          Printf.eprintf "FAILED: %s\n%s\n" name (Printexc.to_string exn);
          exit 1)
    [
      ("empty", test_empty);
      ("push_and_get_across_tail_boundaries", test_push_and_get_across_tail_boundaries);
      ("persistent_push_keeps_old_vector", test_persistent_push_keeps_old_vector);
      ( "set_updates_tail_and_trie_without_mutating_old_vector",
        test_set_updates_tail_and_trie_without_mutating_old_vector );
      ("set_at_count_appends_like_clojure_assocn", test_set_at_count_appends_like_clojure_assocn);
      ("pop_and_peek_across_boundaries", test_pop_and_peek_across_boundaries);
      ("invalid_indices", test_invalid_indices);
      ("large_roundtrip", test_large_roundtrip);
      ("of_list_large_allocation_uses_array_conversion", test_of_list_large_allocation_uses_array_conversion);
      ("of_array_and_to_array_roundtrip", test_of_array_and_to_array_roundtrip);
      ( "array_conversions_do_not_share_mutable_storage",
        test_array_conversions_do_not_share_mutable_storage );
      ( "of_array_large_allocation_is_linear_in_array_storage",
        test_of_array_large_allocation_is_linear_in_array_storage );
      ( "to_array_large_allocation_avoids_intermediate_list",
        test_to_array_large_allocation_avoids_intermediate_list );
      ("to_array_supports_views", test_to_array_supports_views);
      ( "materializing_view_for_push_uses_linear_array_storage",
        test_materializing_view_for_push_uses_linear_array_storage );
      ("of_seq_and_to_seq_roundtrip", test_of_seq_and_to_seq_roundtrip);
      ("of_seq_consumes_input_once_in_order", test_of_seq_consumes_input_once_in_order);
      ("to_seq_supports_views", test_to_seq_supports_views);
      ("fold_left_visits_values_in_order", test_fold_left_visits_values_in_order);
      ("fold_left_empty_keeps_accumulator", test_fold_left_empty_keeps_accumulator);
      ("map_preserves_order_and_length", test_map_preserves_order_and_length);
      ("map_supports_type_changes_and_keeps_original", test_map_supports_type_changes_and_keeps_original);
      ("subvec_extracts_half_open_range", test_subvec_extracts_half_open_range);
      ("subvec_rejects_invalid_ranges", test_subvec_rejects_invalid_ranges);
      ("concat_preserves_order_and_operands", test_concat_preserves_order_and_operands);
      ("concat_handles_empty_vectors", test_concat_handles_empty_vectors);
      ("views_support_vector_operations", test_views_support_vector_operations);
      ("deep_concat_traversal_is_stack_safe", test_deep_concat_traversal_is_stack_safe);
      ("deep_concat_to_array_is_stack_safe", test_deep_concat_to_array_is_stack_safe);
    ]
