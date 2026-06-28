open Ivector

let check name condition =
  if not condition then failwith name

let check_int name expected actual =
  if expected <> actual then
    failwith (Printf.sprintf "%s: expected %d, got %d" name expected actual)

let check_list name expected actual =
  if expected <> actual then failwith name

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
      ("fold_left_visits_values_in_order", test_fold_left_visits_values_in_order);
      ("fold_left_empty_keeps_accumulator", test_fold_left_empty_keeps_accumulator);
      ("map_preserves_order_and_length", test_map_preserves_order_and_length);
      ("map_supports_type_changes_and_keeps_original", test_map_supports_type_changes_and_keeps_original);
    ]
