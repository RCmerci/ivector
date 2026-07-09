open Rrbvec

let failf fmt = Printf.ksprintf (fun message -> Alcotest.fail message) fmt

let check_raises_invalid_arg name f =
  match f () with
  | exception Invalid_argument _ -> ()
  | exception exn ->
      Alcotest.failf "%s: expected Invalid_argument, got %s" name
        (Printexc.to_string exn)
  | _ -> Alcotest.failf "%s: expected Invalid_argument" name

let check_raises_not_found name f =
  match f () with
  | exception Not_found -> ()
  | exception exn ->
      Alcotest.failf "%s: expected Not_found, got %s" name
        (Printexc.to_string exn)
  | _ -> Alcotest.failf "%s: expected Not_found" name

let expect_some name = function
  | Some value -> value
  | None -> Alcotest.failf "%s: expected Some" name

let expect_none name = function
  | None -> ()
  | Some _ -> Alcotest.failf "%s: expected None" name

let nth values index = Rrbvec.nth values index
let pop_back values = expect_some "pop_back" (Rrbvec.pop_back values)
let pop_front values = expect_some "pop_front" (Rrbvec.pop_front values)
let peek_front values = expect_some "peek_front" (Rrbvec.peek_front values)
let peek_back values = expect_some "peek_back" (Rrbvec.peek_back values)

let subvec values start stop =
  expect_some "subvec" (Rrbvec.subvec values start stop)

let check_invariants name v =
  try invariants v
  with exn ->
    Alcotest.failf "%s: invariant failure: %s" name (Printexc.to_string exn)

let list_slice values start stop =
  let rec drop count values =
    if count = 0 then values
    else match values with [] -> [] | _ :: rest -> drop (count - 1) rest
  in
  let rec take count values acc =
    if count = 0 then List.rev acc
    else
      match values with
      | [] -> invalid_arg "not enough values"
      | value :: rest -> take (count - 1) rest (value :: acc)
  in
  take (stop - start) (drop start values) []

let list_set values index value =
  List.mapi (fun i current -> if i = index then value else current) values

let list_drop_last values =
  match List.rev values with
  | [] -> invalid_arg "empty list"
  | _ :: rest -> List.rev rest

let string_of_int_list values =
  "[" ^ String.concat "; " (List.map string_of_int values) ^ "]"

let non_negative_mod value bound =
  let remainder = value mod bound in
  if remainder < 0 then remainder + bound else remainder

let normalize_existing_index values raw_index =
  non_negative_mod raw_index (List.length values)

let normalize_subvec_bounds values raw_start raw_length =
  let length = List.length values in
  if length = 0 then (0, 0)
  else
    let start = non_negative_mod raw_start (length + 1) in
    let stop = start + non_negative_mod raw_length (length - start + 1) in
    (start, stop)

type mapper = Add of int | Subtract_from of int | Negate | Half
type indexed_mapper = Add_index | Subtract_index | Index_minus_value

type predicate =
  | Even
  | Odd
  | Non_negative
  | Less_than of int
  | Greater_than of int
  | Mod_eq of int * int

type find_mapper = First_multiple of int | First_positive_offset of int
type concat_mapper = Singleton of mapper | Keep_non_negative | Drop_all
type sort_order = Ascending | Descending
type partition_side = Left | Right | Joined

type operation =
  | Push_back of int
  | Push_front of int
  | Pop_back
  | Pop_front
  | Set of int * int
  | Get of int
  | Peek_back
  | Peek_front
  | Length
  | Is_empty
  | To_list
  | To_array
  | Fold_left_sum
  | Fold_right_cons
  | Map of mapper
  | Filter of predicate
  | Filter_map of predicate * mapper
  | Concat_map of concat_mapper
  | Map2_indexed_right of int
  | Combine_indexed_right of int
  | Exists of predicate
  | For_all of predicate
  | Find of predicate
  | Find_opt of predicate
  | Find_map of find_mapper
  | Mem of int
  | Iter
  | Iteri
  | Mapi of indexed_mapper
  | Rev
  | Init of int * mapper
  | Sort of sort_order
  | Sort_uniq of sort_order
  | Partition of predicate * partition_side
  | Subvec of int * int
  | Append of int list
  | Prepend of int list
  | Concat_right of int list
  | Concat_left of int list
  | Append_list of int list
  | Append_array of int list
  | Prepend_list of int list
  | Prepend_array of int list
  | Of_list of int list
  | Of_array of int list

let apply_mapper mapper value =
  match mapper with
  | Add offset -> value + offset
  | Subtract_from base -> base - value
  | Negate -> -value
  | Half -> value / 2

let apply_indexed_mapper mapper index value =
  match mapper with
  | Add_index -> value + index
  | Subtract_index -> value - index
  | Index_minus_value -> index - value

let apply_predicate predicate value =
  match predicate with
  | Even -> value mod 2 = 0
  | Odd -> value mod 2 <> 0
  | Non_negative -> value >= 0
  | Less_than limit -> value < limit
  | Greater_than limit -> value > limit
  | Mod_eq (modulus, remainder) -> non_negative_mod value modulus = remainder

let apply_find_mapper mapper value =
  match mapper with
  | First_multiple modulus ->
      if value <> 0 && value mod modulus = 0 then Some (value / modulus)
      else None
  | First_positive_offset offset ->
      if value > 0 then Some (value + offset) else None

let apply_concat_mapper mapper value =
  match mapper with
  | Singleton mapper -> [ apply_mapper mapper value ]
  | Keep_non_negative -> if value >= 0 then [ value ] else []
  | Drop_all -> []

let compare_for_order order =
  match order with
  | Ascending -> compare
  | Descending -> fun left right -> compare right left

let string_of_mapper = function
  | Add offset -> Printf.sprintf "Add %d" offset
  | Subtract_from base -> Printf.sprintf "Subtract_from %d" base
  | Negate -> "Negate"
  | Half -> "Half"

let string_of_indexed_mapper = function
  | Add_index -> "Add_index"
  | Subtract_index -> "Subtract_index"
  | Index_minus_value -> "Index_minus_value"

let string_of_predicate = function
  | Even -> "Even"
  | Odd -> "Odd"
  | Non_negative -> "Non_negative"
  | Less_than limit -> Printf.sprintf "Less_than %d" limit
  | Greater_than limit -> Printf.sprintf "Greater_than %d" limit
  | Mod_eq (modulus, remainder) ->
      Printf.sprintf "Mod_eq (%d, %d)" modulus remainder

let string_of_find_mapper = function
  | First_multiple modulus -> Printf.sprintf "First_multiple %d" modulus
  | First_positive_offset offset ->
      Printf.sprintf "First_positive_offset %d" offset

let string_of_concat_mapper = function
  | Singleton mapper ->
      Printf.sprintf "Singleton (%s)" (string_of_mapper mapper)
  | Keep_non_negative -> "Keep_non_negative"
  | Drop_all -> "Drop_all"

let string_of_sort_order = function
  | Ascending -> "Ascending"
  | Descending -> "Descending"

let string_of_partition_side = function
  | Left -> "Left"
  | Right -> "Right"
  | Joined -> "Joined"

let string_of_operation = function
  | Push_back value -> Printf.sprintf "Push_back %d" value
  | Push_front value -> Printf.sprintf "Push_front %d" value
  | Pop_back -> "Pop_back"
  | Pop_front -> "Pop_front"
  | Set (index, value) -> Printf.sprintf "Set (%d, %d)" index value
  | Get index -> Printf.sprintf "Get %d" index
  | Peek_back -> "Peek_back"
  | Peek_front -> "Peek_front"
  | Length -> "Length"
  | Is_empty -> "Is_empty"
  | To_list -> "To_list"
  | To_array -> "To_array"
  | Fold_left_sum -> "Fold_left_sum"
  | Fold_right_cons -> "Fold_right_cons"
  | Map mapper -> Printf.sprintf "Map (%s)" (string_of_mapper mapper)
  | Filter predicate ->
      Printf.sprintf "Filter (%s)" (string_of_predicate predicate)
  | Filter_map (predicate, mapper) ->
      Printf.sprintf "Filter_map (%s, %s)"
        (string_of_predicate predicate)
        (string_of_mapper mapper)
  | Concat_map mapper ->
      Printf.sprintf "Concat_map (%s)" (string_of_concat_mapper mapper)
  | Map2_indexed_right offset -> Printf.sprintf "Map2_indexed_right %d" offset
  | Combine_indexed_right offset ->
      Printf.sprintf "Combine_indexed_right %d" offset
  | Exists predicate ->
      Printf.sprintf "Exists (%s)" (string_of_predicate predicate)
  | For_all predicate ->
      Printf.sprintf "For_all (%s)" (string_of_predicate predicate)
  | Find predicate -> Printf.sprintf "Find (%s)" (string_of_predicate predicate)
  | Find_opt predicate ->
      Printf.sprintf "Find_opt (%s)" (string_of_predicate predicate)
  | Find_map mapper ->
      Printf.sprintf "Find_map (%s)" (string_of_find_mapper mapper)
  | Mem value -> Printf.sprintf "Mem %d" value
  | Iter -> "Iter"
  | Iteri -> "Iteri"
  | Mapi mapper -> Printf.sprintf "Mapi (%s)" (string_of_indexed_mapper mapper)
  | Rev -> "Rev"
  | Init (length, mapper) ->
      Printf.sprintf "Init (%d, %s)" length (string_of_mapper mapper)
  | Sort order -> Printf.sprintf "Sort (%s)" (string_of_sort_order order)
  | Sort_uniq order ->
      Printf.sprintf "Sort_uniq (%s)" (string_of_sort_order order)
  | Partition (predicate, side) ->
      Printf.sprintf "Partition (%s, %s)"
        (string_of_predicate predicate)
        (string_of_partition_side side)
  | Subvec (start, length) -> Printf.sprintf "Subvec (%d, %d)" start length
  | Append values -> Printf.sprintf "Append %s" (string_of_int_list values)
  | Prepend values -> Printf.sprintf "Prepend %s" (string_of_int_list values)
  | Concat_right values ->
      Printf.sprintf "Concat_right %s" (string_of_int_list values)
  | Concat_left values ->
      Printf.sprintf "Concat_left %s" (string_of_int_list values)
  | Append_list values ->
      Printf.sprintf "Append_list %s" (string_of_int_list values)
  | Append_array values ->
      Printf.sprintf "Append_array %s" (string_of_int_list values)
  | Prepend_list values ->
      Printf.sprintf "Prepend_list %s" (string_of_int_list values)
  | Prepend_array values ->
      Printf.sprintf "Prepend_array %s" (string_of_int_list values)
  | Of_list values -> Printf.sprintf "Of_list %s" (string_of_int_list values)
  | Of_array values -> Printf.sprintf "Of_array %s" (string_of_int_list values)

let string_of_operations operations =
  operations
  |> List.mapi (fun index operation ->
      Printf.sprintf "%d: %s" index (string_of_operation operation))
  |> String.concat "\n"

let check_property_state step operation values expected =
  let label =
    Printf.sprintf "property step %d after %s" step
      (string_of_operation operation)
  in
  check_invariants label values;
  let actual = to_list values in
  if actual <> expected then
    failf "%s: expected %s, got %s" label
      (string_of_int_list expected)
      (string_of_int_list actual)

let check_bool_result step operation name expected actual =
  if actual <> expected then
    failf "property step %d %s %s: expected %b, got %b" step
      (string_of_operation operation)
      name expected actual

let check_int_result step operation name expected actual =
  if actual <> expected then
    failf "property step %d %s %s: expected %d, got %d" step
      (string_of_operation operation)
      name expected actual

let check_int_list_result step operation name expected actual =
  if actual <> expected then
    failf "property step %d %s %s: expected %s, got %s" step
      (string_of_operation operation)
      name
      (string_of_int_list expected)
      (string_of_int_list actual)

let check_int_option_result step operation name expected actual =
  if actual <> expected then
    failf "property step %d %s %s: expected %s, got %s" step
      (string_of_operation operation)
      name
      (match expected with
      | None -> "None"
      | Some value -> Printf.sprintf "Some %d" value)
      (match actual with
      | None -> "None"
      | Some value -> Printf.sprintf "Some %d" value)

let indexed_right offset expected =
  List.mapi (fun index _ -> index + offset) expected

let apply_operation step values expected operation =
  let values, expected =
    match operation with
    | Push_back value -> (push_back values value, expected @ [ value ])
    | Push_front value -> (push_front values value, value :: expected)
    | Pop_back -> (
        match expected with
        | [] ->
            expect_none "property pop_back empty" (Rrbvec.pop_back values);
            (values, expected)
        | _ ->
            let expected_value = List.hd (List.rev expected) in
            let value, values = pop_back values in
            check_int_result step operation "value" expected_value value;
            (values, list_drop_last expected))
    | Pop_front -> (
        match expected with
        | [] ->
            expect_none "property pop_front empty" (Rrbvec.pop_front values);
            (values, expected)
        | expected_value :: rest ->
            let value, values = pop_front values in
            check_int_result step operation "value" expected_value value;
            (values, rest))
    | Set (raw_index, value) ->
        if expected = [] then (
          check_raises_invalid_arg "property set empty" (fun () ->
              ignore (Rrbvec.set values 0 value));
          (values, expected))
        else
          let index = normalize_existing_index expected raw_index in
          let expected = list_set expected index value in
          (Rrbvec.set values index value, expected)
    | Get raw_index -> begin
        if expected = [] then begin
          check_raises_invalid_arg "property nth empty" (fun () ->
              ignore (Rrbvec.nth values 0));
          expect_none "property nth_opt empty" (Rrbvec.nth_opt values 0)
        end
        else begin
          let index = normalize_existing_index expected raw_index in
          let expected_value = List.nth expected index in
          check_int_result step operation "nth" expected_value
            (nth values index);
          check_int_option_result step operation "nth_opt" (Some expected_value)
            (Rrbvec.nth_opt values index)
        end;
        (values, expected)
      end
    | Peek_back ->
        begin match expected with
        | [] -> expect_none "property peek_back empty" (Rrbvec.peek_back values)
        | _ ->
            let expected_value = List.hd (List.rev expected) in
            check_int_result step operation "value" expected_value
              (peek_back values)
        end;
        (values, expected)
    | Peek_front ->
        begin match expected with
        | [] ->
            expect_none "property peek_front empty" (Rrbvec.peek_front values)
        | expected_value :: _ ->
            check_int_result step operation "value" expected_value
              (peek_front values)
        end;
        (values, expected)
    | Length ->
        check_int_result step operation "length" (List.length expected)
          (Rrbvec.length values);
        (values, expected)
    | Is_empty ->
        check_bool_result step operation "is_empty" (expected = [])
          (Rrbvec.is_empty values);
        (values, expected)
    | To_list ->
        check_int_list_result step operation "to_list" expected
          (Rrbvec.to_list values);
        (values, expected)
    | To_array ->
        check_int_list_result step operation "to_array" expected
          (Array.to_list (Rrbvec.to_array values));
        (values, expected)
    | Fold_left_sum ->
        check_int_result step operation "fold_left"
          (List.fold_left ( + ) 0 expected)
          (Rrbvec.fold_left ( + ) 0 values);
        (values, expected)
    | Fold_right_cons ->
        check_int_list_result step operation "fold_right"
          (List.fold_right (fun value acc -> value :: acc) expected [])
          (Rrbvec.fold_right (fun value acc -> value :: acc) values []);
        (values, expected)
    | Map mapper ->
        ( Rrbvec.map (apply_mapper mapper) values,
          List.map (apply_mapper mapper) expected )
    | Filter predicate ->
        ( Rrbvec.filter (apply_predicate predicate) values,
          List.filter (apply_predicate predicate) expected )
    | Filter_map (predicate, mapper) ->
        let f value =
          if apply_predicate predicate value then
            Some (apply_mapper mapper value)
          else None
        in
        (Rrbvec.filter_map f values, List.filter_map f expected)
    | Concat_map mapper ->
        let vector_f value =
          Rrbvec.of_list (apply_concat_mapper mapper value)
        in
        let list_f value = apply_concat_mapper mapper value in
        (Rrbvec.concat_map vector_f values, List.concat_map list_f expected)
    | Map2_indexed_right offset ->
        let right = indexed_right offset expected in
        ( Rrbvec.map2 ( + ) values (Rrbvec.of_list right),
          List.map2 ( + ) expected right )
    | Combine_indexed_right offset ->
        let right = indexed_right offset expected in
        let actual =
          Rrbvec.combine values (Rrbvec.of_list right) |> Rrbvec.to_list
        in
        let expected_pairs = List.combine expected right in
        if actual <> expected_pairs then
          Alcotest.failf "property step %d %s combine mismatch" step
            (string_of_operation operation);
        (values, expected)
    | Exists predicate ->
        check_bool_result step operation "exists"
          (List.exists (apply_predicate predicate) expected)
          (Rrbvec.exists (apply_predicate predicate) values);
        (values, expected)
    | For_all predicate ->
        check_bool_result step operation "for_all"
          (List.for_all (apply_predicate predicate) expected)
          (Rrbvec.for_all (apply_predicate predicate) values);
        (values, expected)
    | Find predicate ->
        (match List.find_opt (apply_predicate predicate) expected with
        | Some expected_value ->
            check_int_result step operation "find" expected_value
              (Rrbvec.find (apply_predicate predicate) values)
        | None ->
            check_raises_not_found "property find missing" (fun () ->
                ignore (Rrbvec.find (apply_predicate predicate) values)));
        (values, expected)
    | Find_opt predicate ->
        check_int_option_result step operation "find_opt"
          (List.find_opt (apply_predicate predicate) expected)
          (Rrbvec.find_opt (apply_predicate predicate) values);
        (values, expected)
    | Find_map mapper ->
        check_int_option_result step operation "find_map"
          (List.find_map (apply_find_mapper mapper) expected)
          (Rrbvec.find_map (apply_find_mapper mapper) values);
        (values, expected)
    | Mem value ->
        check_bool_result step operation "mem" (List.mem value expected)
          (Rrbvec.mem value values);
        (values, expected)
    | Iter ->
        let actual = ref [] in
        Rrbvec.iter (fun value -> actual := value :: !actual) values;
        check_int_list_result step operation "iter" expected (List.rev !actual);
        (values, expected)
    | Iteri ->
        let actual = ref [] in
        Rrbvec.iteri
          (fun index value -> actual := (index + value) :: !actual)
          values;
        check_int_list_result step operation "iteri"
          (List.mapi (fun index value -> index + value) expected)
          (List.rev !actual);
        (values, expected)
    | Mapi mapper ->
        ( Rrbvec.mapi (apply_indexed_mapper mapper) values,
          List.mapi (apply_indexed_mapper mapper) expected )
    | Rev -> (Rrbvec.rev values, List.rev expected)
    | Init (raw_length, mapper) ->
        let length = non_negative_mod raw_length 129 in
        ( Rrbvec.init length (fun index -> apply_mapper mapper index),
          List.init length (fun index -> apply_mapper mapper index) )
    | Sort order ->
        let compare = compare_for_order order in
        (Rrbvec.sort compare values, List.sort compare expected)
    | Sort_uniq order ->
        let compare = compare_for_order order in
        (Rrbvec.sort_uniq compare values, List.sort_uniq compare expected)
    | Partition (predicate, side) ->
        let expected_left, expected_right =
          List.partition (apply_predicate predicate) expected
        in
        let actual_left, actual_right =
          Rrbvec.partition (apply_predicate predicate) values
        in
        check_invariants "property partition left" actual_left;
        check_invariants "property partition right" actual_right;
        check_int_list_result step operation "partition left" expected_left
          (Rrbvec.to_list actual_left);
        check_int_list_result step operation "partition right" expected_right
          (Rrbvec.to_list actual_right);
        begin match side with
        | Left -> (actual_left, expected_left)
        | Right -> (actual_right, expected_right)
        | Joined ->
            ( Rrbvec.append actual_left actual_right,
              expected_left @ expected_right )
        end
    | Subvec (raw_start, raw_length) ->
        let start, stop =
          normalize_subvec_bounds expected raw_start raw_length
        in
        (subvec values start stop, list_slice expected start stop)
    | Append right ->
        (Rrbvec.append values (Rrbvec.of_list right), expected @ right)
    | Prepend left ->
        (Rrbvec.prepend (Rrbvec.of_list left) values, left @ expected)
    | Concat_right right ->
        (Rrbvec.concat values (Rrbvec.of_list right), expected @ right)
    | Concat_left left ->
        (Rrbvec.concat (Rrbvec.of_list left) values, left @ expected)
    | Append_list right -> (Rrbvec.append_list values right, expected @ right)
    | Append_array right ->
        (Rrbvec.append_array values (Array.of_list right), expected @ right)
    | Prepend_list left -> (Rrbvec.prepend_list values left, left @ expected)
    | Prepend_array left ->
        (Rrbvec.prepend_array values (Array.of_list left), left @ expected)
    | Of_list values -> (Rrbvec.of_list values, values)
    | Of_array values -> (Rrbvec.of_array (Array.of_list values), values)
  in
  check_property_state step operation values expected;
  (values, expected)

let mapper_gen =
  let open QCheck2.Gen in
  oneof
    [
      map (fun offset -> Add offset) (int_range (-20) 20);
      map (fun base -> Subtract_from base) (int_range (-20) 20);
      return Negate;
      return Half;
    ]

let indexed_mapper_gen =
  let open QCheck2.Gen in
  oneof [ return Add_index; return Subtract_index; return Index_minus_value ]

let predicate_gen =
  let open QCheck2.Gen in
  oneof
    [
      return Even;
      return Odd;
      return Non_negative;
      map (fun limit -> Less_than limit) (int_range (-50) 50);
      map (fun limit -> Greater_than limit) (int_range (-50) 50);
      map2
        (fun modulus remainder -> Mod_eq (modulus, remainder))
        (int_range 1 9) (int_range 0 8);
    ]

let find_mapper_gen =
  let open QCheck2.Gen in
  oneof
    [
      map (fun modulus -> First_multiple modulus) (int_range 1 9);
      map (fun offset -> First_positive_offset offset) (int_range (-20) 20);
    ]

let concat_mapper_gen =
  let open QCheck2.Gen in
  oneof
    [
      map (fun mapper -> Singleton mapper) mapper_gen;
      return Keep_non_negative;
      return Drop_all;
    ]

let sort_order_gen =
  let open QCheck2.Gen in
  oneof [ return Ascending; return Descending ]

let partition_side_gen =
  let open QCheck2.Gen in
  oneof [ return Left; return Right; return Joined ]

let operation_gen =
  let open QCheck2.Gen in
  let value = int_range (-10_000) 10_000 in
  let values = list_size (int_bound 8) value in
  oneof_weighted
    [
      (8, map (fun value -> Push_back value) value);
      (8, map (fun value -> Push_front value) value);
      (5, return Pop_back);
      (5, return Pop_front);
      (5, map2 (fun index value -> Set (index, value)) int value);
      (3, map (fun index -> Get index) int);
      (2, return Peek_back);
      (2, return Peek_front);
      (2, return Length);
      (2, return Is_empty);
      (2, return To_list);
      (2, return To_array);
      (2, return Fold_left_sum);
      (2, return Fold_right_cons);
      (4, map (fun mapper -> Map mapper) mapper_gen);
      (4, map (fun predicate -> Filter predicate) predicate_gen);
      ( 4,
        map2
          (fun predicate mapper -> Filter_map (predicate, mapper))
          predicate_gen mapper_gen );
      (3, map (fun mapper -> Concat_map mapper) concat_mapper_gen);
      (3, map (fun offset -> Map2_indexed_right offset) (int_range (-20) 20));
      (2, map (fun offset -> Combine_indexed_right offset) (int_range (-20) 20));
      (2, map (fun predicate -> Exists predicate) predicate_gen);
      (2, map (fun predicate -> For_all predicate) predicate_gen);
      (2, map (fun predicate -> Find predicate) predicate_gen);
      (2, map (fun predicate -> Find_opt predicate) predicate_gen);
      (2, map (fun mapper -> Find_map mapper) find_mapper_gen);
      (2, map (fun value -> Mem value) value);
      (2, return Iter);
      (2, return Iteri);
      (3, map (fun mapper -> Mapi mapper) indexed_mapper_gen);
      (3, return Rev);
      (3, map2 (fun length mapper -> Init (length, mapper)) int mapper_gen);
      (3, map (fun order -> Sort order) sort_order_gen);
      (3, map (fun order -> Sort_uniq order) sort_order_gen);
      ( 3,
        map2
          (fun predicate side -> Partition (predicate, side))
          predicate_gen partition_side_gen );
      (4, map2 (fun start length -> Subvec (start, length)) int int);
      (4, map (fun values -> Append values) values);
      (4, map (fun values -> Prepend values) values);
      (4, map (fun values -> Concat_right values) values);
      (4, map (fun values -> Concat_left values) values);
      (3, map (fun values -> Append_list values) values);
      (3, map (fun values -> Append_array values) values);
      (3, map (fun values -> Prepend_list values) values);
      (3, map (fun values -> Prepend_array values) values);
      (2, map (fun values -> Of_list values) values);
      (2, map (fun values -> Of_array values) values);
    ]

let property_public_operations_preserve_invariants =
  QCheck2.Test.make ~name:"public operations preserve invariants" ~count:2_000
    ~print:string_of_operations
    QCheck2.Gen.(list_size (int_range 0 400) operation_gen)
    (fun operations ->
      check_invariants "property initial state" empty;
      ignore
        (List.fold_left
           (fun (step, values, expected) operation ->
             let values, expected =
               apply_operation step values expected operation
             in
             (step + 1, values, expected))
           (0, empty, []) operations);
      true)

let () =
  Alcotest.run "rrbvec qcheck"
    [
      ( "properties",
        [
          QCheck_alcotest.to_alcotest ~speed_level:`Quick
            property_public_operations_preserve_invariants;
        ] );
    ]
