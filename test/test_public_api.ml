open Rrbvec

let test_case name test = Alcotest.test_case name `Quick test

let check_int_list name expected actual =
  Alcotest.(check (list int)) name expected actual

let check_bool name expected actual = Alcotest.(check bool) name expected actual

let check_int name expected actual = Alcotest.(check int) name expected actual

let check_int_option name expected actual =
  Alcotest.(check (option int)) name expected actual

let check_string_option name expected actual =
  Alcotest.(check (option string)) name expected actual

let check_string_list name expected actual =
  Alcotest.(check (list string)) name expected actual

let check_pair_list name expected actual =
  Alcotest.(check (list (pair int string))) name expected actual

let check_allocated_less_than name limit actual =
  if not (actual < limit) then
    Alcotest.failf "%s: expected < %.0f bytes, got %.0f bytes" name limit
      actual

let measure_allocated_bytes f =
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let result = f () in
  let allocated = Gc.allocated_bytes () -. before in
  (result, allocated)

let check_partition name (expected_left, expected_right)
    (actual_left, actual_right) =
  check_int_list (name ^ " left") expected_left (to_list actual_left);
  check_int_list (name ^ " right") expected_right (to_list actual_right)

let check_invalid_arg name f =
  match f () with
  | exception Invalid_argument _ -> ()
  | exception exn ->
      Alcotest.failf "%s: expected Invalid_argument, got %s" name
        (Printexc.to_string exn)
  | _ -> Alcotest.failf "%s: expected Invalid_argument" name

let check_not_found name f =
  match f () with
  | exception Not_found -> ()
  | exception exn ->
      Alcotest.failf "%s: expected Not_found, got %s" name
        (Printexc.to_string exn)
  | _ -> Alcotest.failf "%s: expected Not_found" name

let range n = List.init n Fun.id

let vector values = of_list values

let compare_case_insensitive left right =
  String.compare
    (String.lowercase_ascii left)
    (String.lowercase_ascii right)

let test_filter_family_matches_list () =
  let values = range 80 in
  let v = vector values in
  let is_kept value = value mod 3 <> 1 in
  check_int_list "filter"
    (List.filter is_kept values)
    (to_list (filter is_kept v));
  check_int_list "filter empty" [] (to_list (filter is_kept empty));
  let filter_map_value value =
    if value mod 4 = 0 then Some (value / 2) else None
  in
  check_int_list "filter_map"
    (List.filter_map filter_map_value values)
    (to_list (filter_map filter_map_value v));
  check_int_list "concat_map"
    (List.concat_map (fun value -> [ value; -value ]) values)
    (to_list (concat_map (fun value -> vector [ value; -value ]) v))

let test_filter_family_evaluates_left_to_right () =
  let values = range 8 in
  let v = vector values in
  let check_visits name list_apply vector_apply =
    let list_seen = ref [] in
    let vector_seen = ref [] in
    ignore (list_apply (fun value -> list_seen := value :: !list_seen));
    ignore (vector_apply (fun value -> vector_seen := value :: !vector_seen));
    check_int_list name (List.rev !list_seen) (List.rev !vector_seen)
  in
  check_visits "filter visits"
    (fun record ->
      List.filter
        (fun value ->
          record value;
          value mod 2 = 0)
        values)
    (fun record -> filter (fun value -> record value; value mod 2 = 0) v);
  check_visits "filter_map visits"
    (fun record ->
      List.filter_map
        (fun value ->
          record value;
          if value mod 2 = 0 then Some value else None)
        values)
    (fun record ->
      filter_map
        (fun value ->
          record value;
          if value mod 2 = 0 then Some value else None)
        v);
  check_visits "concat_map visits"
    (fun record ->
      List.concat_map
        (fun value ->
          record value;
          [ value ])
        values)
    (fun record ->
      concat_map
        (fun value ->
          record value;
          vector [ value ])
        v)

let test_pairwise_apis_match_list () =
  let left_values = range 70 in
  let right_values = List.map string_of_int left_values in
  let left = vector left_values in
  let right = vector right_values in
  check_int_list "map2"
    (List.map2 (fun left right -> left + String.length right) left_values
       right_values)
    (to_list (map2 (fun left right -> left + String.length right) left right));
  check_pair_list "combine"
    (List.combine left_values right_values)
    (to_list (combine left right));
  check_invalid_arg "map2 left longer" (fun () ->
      ignore (map2 ( + ) (vector [ 1; 2 ]) (vector [ 1 ])));
  check_invalid_arg "map2 right longer" (fun () ->
      ignore (map2 ( + ) (vector [ 1 ]) (vector [ 1; 2 ])));
  check_invalid_arg "combine length mismatch" (fun () ->
      ignore (combine (vector [ 1; 2 ]) (vector [ "1" ])))

let test_pairwise_traversal_apis_match_list () =
  let left_values = [ 1; 2; 3; 4 ] in
  let right_values = [ "a"; "bb"; "ccc"; "dddd" ] in
  let left = vector left_values in
  let right = vector right_values in
  let list_seen = ref [] in
  let vector_seen = ref [] in
  List.iter2
    (fun left right -> list_seen := (left, right) :: !list_seen)
    left_values right_values;
  iter2
    (fun left right -> vector_seen := (left, right) :: !vector_seen)
    left right;
  Alcotest.(check (list (pair int string)))
    "iter2" (List.rev !list_seen) (List.rev !vector_seen);
  let fold_left f =
    f (fun acc left right -> acc + left + String.length right) 0
  in
  check_int "fold_left2"
    (fold_left (fun f acc -> List.fold_left2 f acc left_values right_values))
    (fold_left (fun f acc -> fold_left2 f acc left right));
  check_bool "for_all2"
    (List.for_all2
       (fun left right -> left = String.length right)
       left_values right_values)
    (for_all2
       (fun left right -> left = String.length right)
       left right);
  check_bool "exists2"
    (List.exists2
       (fun left right -> left + String.length right = 6)
       left_values right_values)
    (exists2
       (fun left right -> left + String.length right = 6)
       left right);
  check_int_list "fold_right2"
    (List.fold_right2
       (fun left right acc -> (left + String.length right) :: acc)
       left_values right_values [])
    (fold_right2
       (fun left right acc -> (left + String.length right) :: acc)
       left right []);
  iter2 (fun _ _ -> Alcotest.fail "iter2 empty callback") empty empty;
  check_int "fold_left2 empty" 7 (fold_left2 (fun acc _ _ -> acc) 7 empty empty);
  check_bool "for_all2 empty" true (for_all2 (fun _ _ -> false) empty empty);
  check_bool "exists2 empty" false (exists2 (fun _ _ -> true) empty empty);
  check_int "fold_right2 empty" 7
    (fold_right2 (fun _ _ acc -> acc) empty empty 7)

let test_pairwise_traversal_apis_reject_length_mismatch_without_calls () =
  let left = vector [ 1; 2 ] in
  let right = vector [ 1 ] in
  let calls = ref 0 in
  let called () = incr calls in
  check_invalid_arg "iter2 length mismatch" (fun () ->
      iter2 (fun _ _ -> called ()) left right);
  check_int "iter2 mismatch calls" 0 !calls;
  check_invalid_arg "fold_left2 length mismatch" (fun () ->
      ignore (fold_left2 (fun acc _ _ -> called (); acc) 0 left right));
  check_int "fold_left2 mismatch calls" 0 !calls;
  check_invalid_arg "for_all2 length mismatch" (fun () ->
      ignore (for_all2 (fun _ _ -> called (); true) left right));
  check_int "for_all2 mismatch calls" 0 !calls;
  check_invalid_arg "exists2 length mismatch" (fun () ->
      ignore (exists2 (fun _ _ -> called (); false) left right));
  check_int "exists2 mismatch calls" 0 !calls;
  check_invalid_arg "fold_right2 length mismatch" (fun () ->
      ignore (fold_right2 (fun _ _ acc -> called (); acc) left right 0));
  check_int "fold_right2 mismatch calls" 0 !calls

let test_pairwise_traversal_apis_preserve_order_and_short_circuit () =
  let values = range 96 in
  let left = of_array (Array.of_list values) in
  let right =
    List.fold_right (fun value acc -> push_front acc value) values empty
  in
  let list_fold_right_seen = ref [] in
  let vector_fold_right_seen = ref [] in
  ignore
    (List.fold_right2
       (fun left right acc ->
         list_fold_right_seen := (left, right) :: !list_fold_right_seen;
         acc + left + right)
       values values 0);
  ignore
    (fold_right2
       (fun left right acc ->
         vector_fold_right_seen := (left, right) :: !vector_fold_right_seen;
         acc + left + right)
       left right 0);
  Alcotest.(check (list (pair int int)))
    "fold_right2 evaluation order" (List.rev !list_fold_right_seen)
    (List.rev !vector_fold_right_seen);
  let check_short_circuit name list_apply vector_apply =
    let list_seen = ref [] in
    let vector_seen = ref [] in
    check_bool (name ^ " result")
      (list_apply (fun left right ->
           list_seen := (left, right) :: !list_seen;
           left < 53))
      (vector_apply (fun left right ->
           vector_seen := (left, right) :: !vector_seen;
           left < 53));
    Alcotest.(check (list (pair int int)))
      (name ^ " order") (List.rev !list_seen) (List.rev !vector_seen)
  in
  check_short_circuit "for_all2"
    (fun predicate -> List.for_all2 predicate values values)
    (fun predicate -> for_all2 predicate left right);
  check_short_circuit "exists2"
    (fun predicate -> List.exists2 (fun l r -> not (predicate l r)) values values)
    (fun predicate -> exists2 (fun l r -> not (predicate l r)) left right)

let test_pairwise_traversal_apis_cross_layout_boundaries () =
  List.iter
    (fun size ->
      let values = range size in
      let left = of_array (Array.of_list values) in
      let right =
        List.fold_right (fun value acc -> push_front acc value) values empty
      in
      let expected_sum = size * (size - 1) in
      let iter_sum = ref 0 in
      iter2 (fun left right -> iter_sum := !iter_sum + left + right) left right;
      check_int ("iter2 boundary " ^ string_of_int size) expected_sum !iter_sum;
      check_int ("fold_left2 boundary " ^ string_of_int size) expected_sum
        (fold_left2 (fun acc left right -> acc + left + right) 0 left right);
      check_bool ("for_all2 boundary " ^ string_of_int size) true
        (for_all2 Int.equal left right);
      check_bool ("exists2 boundary " ^ string_of_int size) (size > 0)
        (exists2 (fun left right -> left = size - 1 && right = left) left right);
      check_int ("fold_right2 boundary " ^ string_of_int size) expected_sum
        (fold_right2 (fun left right acc -> acc + left + right) left right 0))
    [ 0; 1; 31; 32; 33; 1_023; 1_024; 1_025 ]

let test_pairwise_apis_large_allocation_is_small () =
  let size = 100_000 in
  let left = of_array (Array.init size Fun.id) in
  let right = of_array (Array.init size Fun.id) in
  let _, iter2_allocated =
    measure_allocated_bytes (fun () -> iter2 (fun _ _ -> ()) left right)
  in
  check_allocated_less_than "large iter2 allocation" 100_000. iter2_allocated;
  let _, fold_left2_allocated =
    measure_allocated_bytes (fun () ->
        fold_left2 (fun acc left right -> acc + left + right) 0 left right)
  in
  check_allocated_less_than "large fold_left2 allocation" 100_000.
    fold_left2_allocated;
  let _, for_all2_allocated =
    measure_allocated_bytes (fun () -> for_all2 Int.equal left right)
  in
  check_allocated_less_than "large for_all2 allocation" 100_000.
    for_all2_allocated;
  let _, exists2_allocated =
    measure_allocated_bytes (fun () ->
        exists2 (fun left right -> left <> right) left right)
  in
  check_allocated_less_than "large exists2 allocation" 100_000.
    exists2_allocated;
  let _, fold_right2_allocated =
    measure_allocated_bytes (fun () ->
        fold_right2 (fun left right acc -> acc + left + right) left right 0)
  in
  check_allocated_less_than "large fold_right2 allocation" 100_000.
    fold_right2_allocated;
  let mapped, map2_allocated =
    measure_allocated_bytes (fun () -> map2 ( + ) left right)
  in
  Private.invariants mapped;
  check_int "large map2 length" size (length mapped);
  check_allocated_less_than "large map2 allocation" 2_000_000. map2_allocated

let test_predicate_and_search_apis_match_list () =
  let values = range 90 in
  let v = vector values in
  let is_multiple_of_17 value = value mod 17 = 0 && value > 0 in
  check_bool "exists" (List.exists is_multiple_of_17 values)
    (exists is_multiple_of_17 v);
  check_bool "exists empty" (List.exists is_multiple_of_17 [])
    (exists is_multiple_of_17 empty);
  check_bool "for_all" (List.for_all (fun value -> value < 100) values)
    (for_all (fun value -> value < 100) v);
  check_bool "for_all false"
    (List.for_all (fun value -> value mod 2 = 0) values)
    (for_all (fun value -> value mod 2 = 0) v);
  check_int "find" (List.find is_multiple_of_17 values)
    (find is_multiple_of_17 v);
  check_int_option "find_opt"
    (List.find_opt (fun value -> value > 120) values)
    (find_opt (fun value -> value > 120) v);
  check_int_option "find_map"
    (List.find_map
       (fun value ->
         if value mod 19 = 0 && value > 0 then Some (value / 19) else None)
       values)
    (find_map
       (fun value ->
         if value mod 19 = 0 && value > 0 then Some (value / 19) else None)
       v);
  check_bool "mem present" (List.mem 42 values) (mem 42 v);
  check_bool "mem absent" (List.mem 142 values) (mem 142 v);
  check_not_found "find missing" (fun () ->
      ignore (find (fun value -> value > 120) v))

let test_short_circuiting_matches_list_order () =
  let values = range 10 in
  let v = vector values in
  let exists_seen = ref [] in
  let list_exists_seen = ref [] in
  let exists_result =
    exists
      (fun value ->
        exists_seen := value :: !exists_seen;
        value = 4)
      v
  in
  let list_exists_result =
    List.exists
      (fun value ->
        list_exists_seen := value :: !list_exists_seen;
        value = 4)
      values
  in
  check_bool "exists short circuit result" list_exists_result exists_result;
  check_int_list "exists short circuit visits" (List.rev !list_exists_seen)
    (List.rev !exists_seen);
  let for_all_seen = ref [] in
  let list_for_all_seen = ref [] in
  let for_all_result =
    for_all
      (fun value ->
        for_all_seen := value :: !for_all_seen;
        value < 4)
      v
  in
  let list_for_all_result =
    List.for_all
      (fun value ->
        list_for_all_seen := value :: !list_for_all_seen;
        value < 4)
      values
  in
  check_bool "for_all short circuit result" list_for_all_result for_all_result;
  check_int_list "for_all short circuit visits" (List.rev !list_for_all_seen)
    (List.rev !for_all_seen)

let test_predicate_and_search_large_allocation_is_small () =
  let size = 100_000 in
  let v = of_array (Array.init size Fun.id) in
  let exists_result, exists_allocated =
    measure_allocated_bytes (fun () -> exists (fun value -> value = size - 1) v)
  in
  check_bool "exists result" true exists_result;
  check_allocated_less_than "large exists allocation" 100.
    exists_allocated;
  let for_all_result, for_all_allocated =
    measure_allocated_bytes (fun () -> for_all (fun value -> value < size) v)
  in
  check_bool "for_all result" true for_all_result;
  check_allocated_less_than "large for_all allocation" 1_000.
    for_all_allocated;
  let find_result, find_allocated =
    measure_allocated_bytes (fun () -> find (fun value -> value = size - 1) v)
  in
  check_int "find result" (size - 1) find_result;
  check_allocated_less_than "large find allocation" 1_000. find_allocated;
  let find_opt_result, find_opt_allocated =
    measure_allocated_bytes (fun () ->
        find_opt (fun value -> value = size - 1) v)
  in
  check_int_option "find_opt result" (Some (size - 1)) find_opt_result;
  check_allocated_less_than "large find_opt allocation" 1_000.
    find_opt_allocated

let test_iter_family_matches_list () =
  let values = range 75 in
  let v = vector values in
  let iter_seen = ref [] in
  iter (fun value -> iter_seen := value :: !iter_seen) v;
  check_int_list "iter order"
    (let seen = ref [] in
     List.iter (fun value -> seen := value :: !seen) values;
     List.rev !seen)
    (List.rev !iter_seen);
  let iteri_seen = ref [] in
  iteri (fun index value -> iteri_seen := (index + value) :: !iteri_seen) v;
  check_int_list "iteri order"
    (let seen = ref [] in
     List.iteri (fun index value -> seen := (index + value) :: !seen) values;
     List.rev !seen)
    (List.rev !iteri_seen);
  check_int_list "mapi"
    (List.mapi (fun index value -> index - value) values)
    (to_list (mapi (fun index value -> index - value) v))

let test_optimized_public_apis_preserve_order () =
  let values = range 96 in
  let v = vector values in
  let check_visits name list_apply vector_apply =
    let list_seen = ref [] in
    let vector_seen = ref [] in
    ignore (list_apply (fun value -> list_seen := value :: !list_seen));
    ignore (vector_apply (fun value -> vector_seen := value :: !vector_seen));
    check_int_list name (List.rev !list_seen) (List.rev !vector_seen)
  in
  check_visits "iter visits"
    (fun record -> List.iter record values)
    (fun record -> iter record v);
  let list_iteri_seen = ref [] in
  let vector_iteri_seen = ref [] in
  List.iteri
    (fun index value -> list_iteri_seen := (index, value) :: !list_iteri_seen)
    values;
  iteri
    (fun index value ->
      vector_iteri_seen := (index, value) :: !vector_iteri_seen)
    v;
  Alcotest.(check (list (pair int int)))
    "iteri visits" (List.rev !list_iteri_seen)
    (List.rev !vector_iteri_seen);
  check_visits "mapi visits"
    (fun record -> List.mapi (fun _ value -> record value; value) values)
    (fun record -> mapi (fun _ value -> record value; value) v);
  check_visits "filter_map visits"
    (fun record ->
      List.filter_map
        (fun value ->
          record value;
          if value mod 3 = 0 then Some value else None)
        values)
    (fun record ->
      filter_map
        (fun value ->
          record value;
          if value mod 3 = 0 then Some value else None)
        v);
  check_visits "partition visits"
    (fun record ->
      List.partition
        (fun value ->
          record value;
          value mod 2 = 0)
        values)
    (fun record ->
      partition
        (fun value ->
          record value;
          value mod 2 = 0)
        v);
  let list_init_seen = ref [] in
  let vector_init_seen = ref [] in
  ignore
    (List.init 96 (fun index -> list_init_seen := index :: !list_init_seen));
  ignore
    (init 96 (fun index -> vector_init_seen := index :: !vector_init_seen));
  check_int_list "init visits" (List.rev !list_init_seen)
    (List.rev !vector_init_seen)

let test_optimized_public_apis_large_allocation_is_small () =
  let size = 100_000 in
  let values = Array.init size Fun.id in
  let v = of_array values in
  let iter_sum, iter_allocated =
    measure_allocated_bytes (fun () ->
        let sum = ref 0 in
        iter (fun value -> sum := !sum + value) v;
        !sum)
  in
  check_int "large iter sum" (size * (size - 1) / 2) iter_sum;
  check_allocated_less_than "large iter allocation" 1_000. iter_allocated;
  let iteri_sum, iteri_allocated =
    measure_allocated_bytes (fun () ->
        let sum = ref 0 in
        iteri (fun index value -> sum := !sum + index + value) v;
        !sum)
  in
  check_int "large iteri sum" (size * (size - 1)) iteri_sum;
  check_allocated_less_than "large iteri allocation" 1_000. iteri_allocated;
  let filtered, filter_allocated =
    measure_allocated_bytes (fun () -> filter (fun value -> value mod 3 <> 1) v)
  in
  Private.invariants filtered;
  check_int "large filter length" (size - (size / 3)) (length filtered);
  check_int "large filter first" 0 (nth filtered 0);
  check_allocated_less_than "large filter allocation" 3_000_000.
    filter_allocated;
  let mapped, mapi_allocated =
    measure_allocated_bytes (fun () ->
        mapi (fun index value -> index + value) v)
  in
  Private.invariants mapped;
  check_int "large mapi length" size (length mapped);
  check_int "large mapi first" 0 (nth mapped 0);
  check_int "large mapi last" ((size - 1) * 2) (nth mapped (size - 1));
  check_allocated_less_than "large mapi allocation" 3_000_000.
    mapi_allocated;
  let initialized, init_allocated =
    measure_allocated_bytes (fun () -> init size Fun.id)
  in
  Private.invariants initialized;
  check_int "large init length" size (length initialized);
  check_int "large init first" 0 (nth initialized 0);
  check_int "large init last" (size - 1) (nth initialized (size - 1));
  check_allocated_less_than "large init allocation" 2_000_000. init_allocated;
  let filter_mapped, filter_map_allocated =
    measure_allocated_bytes (fun () ->
        filter_map
          (fun value -> if value mod 4 = 0 then Some (value / 2) else None)
          v)
  in
  Private.invariants filter_mapped;
  check_int "large filter_map length" (size / 4) (length filter_mapped);
  check_int "large filter_map first" 0 (nth filter_mapped 0);
  check_int "large filter_map last" ((size - 4) / 2)
    (nth filter_mapped (length filter_mapped - 1));
  check_allocated_less_than "large filter_map allocation" 1_500_000.
    filter_map_allocated;
  let (partition_left, partition_right), partition_allocated =
    measure_allocated_bytes (fun () ->
        partition (fun value -> value mod 2 = 0) v)
  in
  Private.invariants partition_left;
  Private.invariants partition_right;
  check_int "large partition left length" (size / 2) (length partition_left);
  check_int "large partition right length" (size / 2) (length partition_right);
  check_int "large partition left first" 0 (nth partition_left 0);
  check_int "large partition right first" 1 (nth partition_right 0);
  check_int "large partition left last" (size - 2)
    (nth partition_left (length partition_left - 1));
  check_int "large partition right last" (size - 1)
    (nth partition_right (length partition_right - 1));
  check_allocated_less_than "large partition allocation" 3_000_000.
    partition_allocated

let test_rev_and_init_match_list () =
  let values = range 73 in
  check_int_list "rev" (List.rev values) (to_list (rev (vector values)));
  check_int_list "rev empty" [] (to_list (rev empty));
  check_int_list "init" (List.init 73 (fun index -> (index * 3) - 5))
    (to_list (init 73 (fun index -> (index * 3) - 5)));
  let seen = ref [] in
  let list_seen = ref [] in
  ignore (init 6 (fun index -> seen := index :: !seen));
  ignore (List.init 6 (fun index -> list_seen := index :: !list_seen));
  check_int_list "init evaluation order" (List.rev !list_seen) (List.rev !seen);
  check_invalid_arg "init negative" (fun () -> ignore (init (-1) Fun.id))

let test_rev_large_allocation_is_leaf_linear () =
  let size = 100_000 in
  let v = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let reversed = rev v in
  let allocated = Gc.allocated_bytes () -. before in
  Private.invariants reversed;
  check_int "large rev length" size (length reversed);
  check_int "large rev first" (size - 1) (nth reversed 0);
  check_int "large rev last" 0 (nth reversed (size - 1));
  check_int "large rev sum" (size * (size - 1) / 2)
    (fold_left ( + ) 0 reversed);
  check_allocated_less_than "large rev allocation" 5_000_000. allocated

let test_sort_family_and_partition_match_list () =
  let values = [ 5; 3; 1; 5; 2; 3; 4; 1; 0; 9; 8; 9; 7; 6 ] in
  let v = vector values in
  let compare_desc left right = Stdlib.compare right left in
  check_int_list "sort ascending" (List.sort Stdlib.compare values)
    (to_list (sort Stdlib.compare v));
  check_int_list "sort descending" (List.sort compare_desc values)
    (to_list (sort compare_desc v));
  check_int_list "sort_uniq" (List.sort_uniq Stdlib.compare values)
    (to_list (sort_uniq Stdlib.compare v));
  check_partition "partition"
    (List.partition (fun value -> value mod 2 = 0) values)
    (partition (fun value -> value mod 2 = 0) v);
  check_partition "partition empty"
    (List.partition (fun value -> value mod 2 = 0) [])
    (partition (fun value -> value mod 2 = 0) empty)

let test_equal_matches_list () =
  let cases =
    [
      ([], []);
      ([], [ 1 ]);
      ([ 1 ], []);
      ([ 1; 2; 3 ], [ 1; 2; 3 ]);
      ([ 1; 2; 3 ], [ 1; 2; 4 ]);
      ([ 1; 2 ], [ 1; 2; 3 ]);
    ]
  in
  List.iteri
    (fun index (left, right) ->
      check_bool ("equal case " ^ string_of_int index)
        (List.equal Int.equal left right)
        (equal Int.equal (vector left) (vector right)))
    cases;
  let values = range 96 in
  let left = vector values in
  let right =
    List.fold_right (fun value acc -> push_front acc value) values empty
  in
  check_bool "equal ignores internal layout" true (equal Int.equal left right);
  let list_seen = ref [] in
  let vector_seen = ref [] in
  let list_result =
    List.equal
      (fun left right ->
        list_seen := (left, right) :: !list_seen;
        left = right)
      [ 1; 2; 3; 4 ] [ 1; 2; 9; 4 ]
  in
  let vector_result =
    equal
      (fun left right ->
        vector_seen := (left, right) :: !vector_seen;
        left = right)
      (vector [ 1; 2; 3; 4 ])
      (vector [ 1; 2; 9; 4 ])
  in
  check_bool "equal short-circuit result" list_result vector_result;
  Alcotest.(check (list (pair int int)))
    "equal comparison order" (List.rev !list_seen) (List.rev !vector_seen);
  check_bool "equal custom predicate" true
    (equal
       (fun left right -> left mod 10 = right mod 10)
       (vector [ 1; 2; 3 ])
       (vector [ 11; 12; 13 ]))

let test_equal_different_lengths_skips_predicate () =
  let calls = ref 0 in
  let result =
    equal
      (fun _ _ ->
        incr calls;
        true)
      (vector [ 1; 2; 3 ])
      (vector [ 1; 2; 3; 4 ])
  in
  check_bool "equal different lengths" false result;
  check_int "equal different lengths predicate calls" 0 !calls

let test_equal_and_compare_cross_layout_boundaries () =
  List.iter
    (fun size ->
      let values = range size in
      let regular = of_array (Array.of_list values) in
      let front_built =
        List.fold_right (fun value acc -> push_front acc value) values empty
      in
      check_bool
        ("equal cross-layout boundary " ^ string_of_int size)
        true
        (equal Int.equal regular front_built);
      check_int
        ("compare cross-layout boundary " ^ string_of_int size)
        0
        (compare Int.compare regular front_built))
    [ 0; 1; 31; 32; 33; 1_023; 1_024; 1_025 ]

let test_equal_large_allocation_is_small () =
  let size = 100_000 in
  let left = of_array (Array.init size Fun.id) in
  let right = of_array (Array.init size Fun.id) in
  let result, allocated =
    measure_allocated_bytes (fun () -> equal Int.equal left right)
  in
  check_bool "large equal result" true result;
  check_allocated_less_than "large equal allocation" 100_000. allocated

let test_compare_matches_list () =
  let cases =
    [
      ([], []);
      ([], [ 1 ]);
      ([ 1 ], []);
      ([ 1; 2; 3 ], [ 1; 2; 3 ]);
      ([ 1; 2; 3 ], [ 1; 2; 4 ]);
      ([ 1; 3 ], [ 1; 2; 9 ]);
      ([ 1; 2 ], [ 1; 2; 3 ]);
      ([ 1; 2; 3 ], [ 1; 2 ]);
    ]
  in
  List.iteri
    (fun index (left, right) ->
      check_int ("compare case " ^ string_of_int index)
        (List.compare Int.compare left right)
        (compare Int.compare (vector left) (vector right)))
    cases;
  let values = range 96 in
  let left = vector values in
  let right =
    List.fold_right (fun value acc -> push_front acc value) values empty
  in
  check_int "compare ignores internal layout" 0 (compare Int.compare left right);
  let custom_compare left right =
    if left = right then 0 else if left < right then -17 else 23
  in
  check_int "compare preserves comparator result"
    (List.compare custom_compare [ 1; 2 ] [ 1; 9 ])
    (compare custom_compare (vector [ 1; 2 ]) (vector [ 1; 9 ]));
  let list_seen = ref [] in
  let vector_seen = ref [] in
  let list_result =
    List.compare
      (fun left right ->
        list_seen := (left, right) :: !list_seen;
        Int.compare left right)
      [ 1; 2; 3; 4 ] [ 1; 2; 9; 4 ]
  in
  let vector_result =
    compare
      (fun left right ->
        vector_seen := (left, right) :: !vector_seen;
        Int.compare left right)
      (vector [ 1; 2; 3; 4 ])
      (vector [ 1; 2; 9; 4 ])
  in
  check_int "compare short-circuit result" list_result vector_result;
  Alcotest.(check (list (pair int int)))
    "compare comparison order" (List.rev !list_seen) (List.rev !vector_seen)

let test_compare_large_allocation_is_small () =
  let size = 100_000 in
  let left = of_array (Array.init size Fun.id) in
  let right = of_array (Array.init size Fun.id) in
  let result, allocated =
    measure_allocated_bytes (fun () -> compare Int.compare left right)
  in
  check_int "large compare result" 0 result;
  check_allocated_less_than "large compare allocation" 100_000. allocated

let test_assoc_family_matches_list () =
  let bindings =
    [ (1, "one"); (2, "first two"); (3, "three"); (2, "second two") ]
  in
  let v = vector bindings in
  Alcotest.(check string)
    "assoc returns leftmost binding"
    (List.assoc 2 bindings) (assoc 2 v);
  check_string_option "assoc_opt returns leftmost binding"
    (List.assoc_opt 2 bindings)
    (assoc_opt 2 v);
  check_bool "mem_assoc present" (List.mem_assoc 3 bindings) (mem_assoc 3 v);
  check_bool "mem_assoc absent" (List.mem_assoc 4 bindings) (mem_assoc 4 v);
  check_string_option "assoc_opt missing" None (assoc_opt 4 v);
  check_string_option "assoc_opt empty" None (assoc_opt 1 empty);
  check_bool "mem_assoc empty" false (mem_assoc 1 empty);
  check_not_found "assoc missing" (fun () -> ignore (assoc 4 v));
  check_not_found "assoc empty" (fun () -> ignore (assoc 1 empty));
  let large_bindings =
    List.init 96 (fun key -> (key, string_of_int key))
    @ [ (17, "later seventeen") ]
  in
  let large = vector large_bindings in
  Alcotest.(check string)
    "assoc traverses a multi-leaf vector"
    (List.assoc 95 large_bindings) (assoc 95 large);
  Alcotest.(check string)
    "assoc keeps the leftmost multi-leaf binding"
    (List.assoc 17 large_bindings) (assoc 17 large);
  let key = ref 7 in
  let structurally_equal_key = ref 7 in
  let physical_bindings =
    vector [ (structurally_equal_key, "structural"); (key, "physical") ]
  in
  Alcotest.(check string)
    "assoc uses structural equality" "structural" (assoc key physical_bindings);
  check_bool "mem_assoc uses structural equality" true
    (mem_assoc key physical_bindings);
  let custom_bindings =
    vector [ ("Alpha", 1); ("beta", 2); ("ALPHA", 3) ]
  in
  check_int "assoc custom comparison keeps leftmost binding" 1
    (assoc ~cmp:compare_case_insensitive "alpha" custom_bindings);
  check_int_option "assoc_opt custom comparison" (Some 2)
    (assoc_opt ~cmp:compare_case_insensitive "BETA" custom_bindings);
  check_bool "mem_assoc custom comparison present" true
    (mem_assoc ~cmp:compare_case_insensitive "Beta" custom_bindings);
  check_bool "mem_assoc custom comparison absent" false
    (mem_assoc ~cmp:compare_case_insensitive "gamma" custom_bindings);
  check_not_found "assoc custom comparison missing" (fun () ->
      ignore (assoc ~cmp:compare_case_insensitive "gamma" custom_bindings));
  let stored_key = vector (range 96) in
  let lookup_key =
    List.fold_right
      (fun value acc -> push_front acc value)
      (range 96) empty
  in
  let vector_bindings = vector [ (stored_key, "same values") ] in
  Alcotest.(check string)
    "assoc supports semantic rrbvec key comparison" "same values"
    (assoc ~cmp:(compare Int.compare) lookup_key vector_bindings)

let test_remove_assoc_family_matches_list () =
  let bindings =
    [ (1, "one"); (2, "first two"); (3, "three"); (2, "second two") ]
  in
  let v = vector bindings in
  List.iter
    (fun key ->
      let actual = remove_assoc key v in
      Private.invariants actual;
      check_pair_list ("remove_assoc " ^ string_of_int key)
        (List.remove_assoc key bindings)
        (to_list actual))
    [ 1; 2; 3; 4 ];
  check_pair_list "remove_assoc empty" [] (to_list (remove_assoc 1 empty));
  let large_bindings =
    List.init 96 (fun key -> (key, string_of_int key))
    @ [ (17, "later seventeen") ]
  in
  let large_removed = remove_assoc 17 (vector large_bindings) in
  Private.invariants large_removed;
  check_pair_list "remove_assoc traverses a multi-leaf vector"
    (List.remove_assoc 17 large_bindings)
    (to_list large_removed);
  let key = ref 7 in
  let structurally_equal_key = ref 7 in
  let physical_bindings =
    vector
      [
        (structurally_equal_key, "structural");
        (key, "physical");
        (key, "later physical");
      ]
  in
  let structurally_removed = remove_assoc key physical_bindings in
  check_string_list "remove_assoc uses structural equality"
    [ "physical"; "later physical" ]
    (List.map snd (to_list structurally_removed));
  let custom_bindings =
    vector [ ("Alpha", 1); ("beta", 2); ("ALPHA", 3) ]
  in
  let custom_removed =
    remove_assoc ~cmp:compare_case_insensitive "alpha" custom_bindings
  in
  Private.invariants custom_removed;
  check_string_list "remove_assoc custom comparison removes leftmost binding"
    [ "beta"; "ALPHA" ]
    (List.map fst (to_list custom_removed));
  check_int_list "remove_assoc custom comparison preserves values" [ 2; 3 ]
    (List.map snd (to_list custom_removed))

let () =
  Alcotest.run "rrbvec public api"
    [
      ( "list-compatible",
        [
          test_case "filter_family_matches_list" test_filter_family_matches_list;
          test_case "filter_family_evaluates_left_to_right"
            test_filter_family_evaluates_left_to_right;
          test_case "pairwise_apis_match_list" test_pairwise_apis_match_list;
          test_case "pairwise_traversal_apis_match_list"
            test_pairwise_traversal_apis_match_list;
          test_case "pairwise_traversal_apis_reject_length_mismatch_without_calls"
            test_pairwise_traversal_apis_reject_length_mismatch_without_calls;
          test_case "pairwise_traversal_apis_preserve_order_and_short_circuit"
            test_pairwise_traversal_apis_preserve_order_and_short_circuit;
          test_case "pairwise_traversal_apis_cross_layout_boundaries"
            test_pairwise_traversal_apis_cross_layout_boundaries;
          test_case "pairwise_apis_large_allocation_is_small"
            test_pairwise_apis_large_allocation_is_small;
          test_case "predicate_and_search_apis_match_list"
            test_predicate_and_search_apis_match_list;
          test_case "short_circuiting_matches_list_order"
            test_short_circuiting_matches_list_order;
          test_case "predicate_and_search_large_allocation_is_small"
            test_predicate_and_search_large_allocation_is_small;
          test_case "iter_family_matches_list" test_iter_family_matches_list;
          test_case "optimized_public_apis_preserve_order"
            test_optimized_public_apis_preserve_order;
          test_case "optimized_public_apis_large_allocation_is_small"
            test_optimized_public_apis_large_allocation_is_small;
          test_case "rev_and_init_match_list" test_rev_and_init_match_list;
          test_case "rev_large_allocation_is_leaf_linear"
            test_rev_large_allocation_is_leaf_linear;
          test_case "sort_family_and_partition_match_list"
            test_sort_family_and_partition_match_list;
          test_case "equal_matches_list" test_equal_matches_list;
          test_case "equal_different_lengths_skips_predicate"
            test_equal_different_lengths_skips_predicate;
          test_case "equal_and_compare_cross_layout_boundaries"
            test_equal_and_compare_cross_layout_boundaries;
          test_case "equal_large_allocation_is_small"
            test_equal_large_allocation_is_small;
          test_case "compare_matches_list" test_compare_matches_list;
          test_case "compare_large_allocation_is_small"
            test_compare_large_allocation_is_small;
          test_case "assoc_family_matches_list" test_assoc_family_matches_list;
          test_case "remove_assoc_family_matches_list"
            test_remove_assoc_family_matches_list;
        ] );
    ]
