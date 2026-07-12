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

let failf fmt = Printf.ksprintf (fun message -> Alcotest.fail message) fmt

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

let expect_some name = function
  | Some value -> value
  | None -> Alcotest.failf "%s: expected Some" name

let expect_none name = function
  | None -> ()
  | Some _ -> Alcotest.failf "%s: expected None" name

let nth values index = Rrbvec.nth values index

let pop_back values = expect_some "pop_back" (Rrbvec.pop_back values)

let pop_front values = expect_some "pop_front" (Rrbvec.pop_front values)

let peek_front values = Rrbvec.peek_front values

let peek_back values = Rrbvec.peek_back values

let subvec values start stop =
  expect_some "subvec" (Rrbvec.subvec values start stop)

let string_contains ~needle haystack =
  let needle_length = String.length needle in
  let haystack_length = String.length haystack in
  let rec loop index =
    index + needle_length <= haystack_length
    && (String.sub haystack index needle_length = needle || loop (index + 1))
  in
  needle_length = 0 || loop 0

let check_invariants name v =
  try Private.invariants v
  with exn ->
    Alcotest.failf "%s: invariant failure: %s" name (Printexc.to_string exn)

let check_invariant_failure_contains name expected_message v =
  match Private.invariants v with
  | () -> Alcotest.failf "%s: expected invariant failure" name
  | exception exn ->
      let message = Printexc.to_string exn in
      if not (string_contains ~needle:expected_message message) then
        Alcotest.failf "%s: expected invariant failure containing %S, got %s" name
          expected_message message

let range n = List.init n Fun.id

let non_negative_mod value modulus =
  let remainder = value mod modulus in
  if remainder < 0 then remainder + modulus else remainder

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
  let root = Obj.field (Obj.field (Obj.repr v) 0) 1 in
  if Obj.is_int root then -1
  else
    match Obj.tag root with
    | 0 -> 0
    | 1 -> (Obj.magic (Obj.field root 3) : int)
    | _ -> Alcotest.fail "unexpected rrb node tag"

let root_child_count v =
  let root = Obj.field (Obj.field (Obj.repr v) 0) 1 in
  if Obj.is_int root then 0
  else
    match Obj.tag root with
    | 0 -> 0
    | 1 -> Obj.size (Obj.field root 0)
    | _ -> Alcotest.fail "unexpected rrb node tag"

let regular_size_table_count v =
  let rec node_size_table_count node =
    if Obj.is_int node then 0
    else
      match Obj.tag node with
      | 0 -> 0
      | 1 ->
          let children = Obj.field node 0 in
          let sizes = Obj.field node 1 in
          let count = ref (if Obj.is_int sizes then 0 else 1) in
          for i = 0 to Obj.size children - 1 do
            count := !count + node_size_table_count (Obj.field children i)
          done;
          !count
      | _ -> Alcotest.fail "unexpected rrb node tag"
  in
  node_size_table_count (Obj.field (Obj.field (Obj.repr v) 0) 1)

let header_tail_length v =
  Array.length (Obj.magic (Obj.field (Obj.field (Obj.repr v) 0) 2) : int array)

let header_tailoff v =
  (Obj.magic (Obj.field (Obj.field (Obj.repr v) 0) 3) : int)

let header_head_length v =
  Array.length (Obj.magic (Obj.field (Obj.field (Obj.repr v) 0) 4) : int array)

let header_tail_array v =
  (Obj.magic (Obj.field (Obj.field (Obj.repr v) 0) 2) : int array)

let header_head_array v =
  (Obj.magic (Obj.field (Obj.field (Obj.repr v) 0) 4) : int array)

let check_same_array name expected actual =
  check name (expected == actual)

let check_node_shared name expected v =
  let root = Obj.field (Obj.field (Obj.repr v) 0) 1 in
  let expected = Obj.repr expected in
  let rec contains node =
    node == expected
    ||
    if Obj.is_int node || Obj.tag node <> 1 then false
    else
      let children = Obj.field node 0 in
      let rec child_contains index =
        index < Obj.size children
        && (contains (Obj.field children index) || child_contains (index + 1))
      in
      child_contains 0
  in
  check name (contains root)

let normalized_left_middle_height v =
  max (internal_height v) (if header_tail_length v = 0 then -1 else 0)

let normalized_right_middle_height v =
  max (internal_height v) (if header_head_length v = 0 then -1 else 0)

let check_concat_height_bound name left right combined =
  let expected_maximum =
    max (normalized_left_middle_height left)
      (normalized_right_middle_height right)
    + 1
  in
  check name (internal_height combined <= expected_maximum)

let rec pairwise_concat = function
  | [] -> empty
  | [ values ] -> values
  | values ->
      let rec concat_pass acc = function
        | left :: right :: rest ->
            concat_pass (concat left right :: acc) rest
        | [ unpaired ] -> List.rev (unpaired :: acc)
        | [] -> List.rev acc
      in
      pairwise_concat (concat_pass [] values)

let check_int_vector name ?(indices = []) expected actual =
  let expected_length = Array.length expected in
  check_invariants (name ^ " structural invariants") actual;
  check_int (name ^ " length") expected_length (length actual);
  check_list (name ^ " complete order") (Array.to_list expected)
    (to_list actual);
  if expected_length > 0 then (
    let check_position label index =
      check_int (name ^ " " ^ label) (Array.unsafe_get expected index)
        (nth actual index)
    in
    check_position "first" 0;
    check_position "middle" (expected_length / 2);
    check_position "last" (expected_length - 1));
  List.iter
    (fun index ->
      if index < 0 || index >= expected_length then
        Alcotest.failf "%s representative index %d is out of bounds" name index;
      check_int
        (Printf.sprintf "%s nth %d" name index)
        (Array.unsafe_get expected index)
        (nth actual index))
    indices;
  check_int (name ^ " fold sum")
    (Array.fold_left ( + ) 0 expected)
    (fold_left ( + ) 0 actual)

type 'a raw_node =
  | Raw_empty
  | Raw_leaf of 'a array
  | Raw_branch of {
      children : 'a raw_node array;
      sizes : int array option;
      count : int;
      height : int;
    }

type 'a raw_vector = {
  count : int;
  root : 'a raw_node;
  tail : 'a array;
  tailoff : int;
  head : 'a array;
}

type 'a raw_t =
  | Raw_empty_vector
  | Raw_vector of 'a raw_vector

let unsafe_vector raw = (Obj.magic (Raw_vector raw) : int t)

let raw_leaf length = Raw_leaf (Array.init length Fun.id)

let raw_leaf_range start length = Raw_leaf (Array.init length (fun i -> start + i))

let raw_branch children =
  let sizes = Array.make (Array.length children) 0 in
  let count = ref 0 in
  let height = ref (-1) in
  Array.iteri
    (fun index child ->
      let child_count, child_height =
        match child with
        | Raw_empty -> (0, -1)
        | Raw_leaf values -> (Array.length values, 0)
        | Raw_branch branch -> (branch.count, branch.height)
      in
      count := !count + child_count;
      height := max !height child_height;
      Array.unsafe_set sizes index !count)
    children;
  Raw_branch
    {
      children;
      sizes = Some sizes;
      count = !count;
      height = !height + 1;
    }

let raw_leaf_from_counter next_value length =
  let start = !next_value in
  next_value := start + length;
  raw_leaf_range start length

let raw_branch_of_leaf_lengths next_value lengths =
  raw_branch
    (Array.of_list
       (List.map (raw_leaf_from_counter next_value) lengths))

let raw_branch_of_full_leaves next_value arity =
  raw_branch
    (Array.init arity (fun _ -> raw_leaf_from_counter next_value rrb_width))

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
  check_list "empty subvec" [] (to_list (subvec v 0 0));
  check_raises_invalid_arg "nth empty" (fun () -> ignore (Rrbvec.nth v 0));
  check_raises_invalid_arg "nth negative" (fun () -> ignore (Rrbvec.nth v (-1)));
  expect_none "nth_opt empty" (Rrbvec.nth_opt v 0);
  expect_none "nth_opt negative" (Rrbvec.nth_opt v (-1));
  expect_none "pop empty" (Rrbvec.pop_back v);
  expect_none "peek_back_opt empty" (Rrbvec.peek_back_opt v);
  expect_none "peek_front_opt empty" (Rrbvec.peek_front_opt v);
  check_raises_invalid_arg "peek_back empty" (fun () ->
      ignore (Rrbvec.peek_back v));
  check_raises_invalid_arg "peek_front empty" (fun () ->
      ignore (Rrbvec.peek_front v));
  expect_none "subvec empty past end" (Rrbvec.subvec v 0 1)

let test_invariants_hold_for_public_operations () =
  List.iter
    (fun size ->
      let values = range size in
      check_invariants "of_list" (of_list values);
      check_invariants "of_array" (of_array (Array.init size Fun.id)))
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
  check_raises_invalid_arg "set at count" (fun () -> ignore (set pushed 1100 42));
  check_invariants "pop" (snd (pop_back pushed));
  check_invariants "subvec" (subvec pushed 17 1090);
  let combined =
    concat (subvec pushed 0 500) (subvec pushed 500 (length pushed))
  in
  check_invariants "concat" combined;
  check_invariants "append_list"
    (append_list pushed [ 1100; 1101 ]);
  check_invariants "append_array"
    (append_array pushed [| 1100; 1101 |]);
  check_invariants "map" (map (( + ) 1) pushed)

let test_invariants_report_malformed_leaf () =
  let malformed =
    raw_vector
      (Raw_branch
         {
           children = [| raw_leaf 0; raw_leaf 1 |];
           sizes = Some [| 0; 1 |];
           count = 1;
           height = 1;
         })
  in
  check_invariant_failure_contains "empty leaf" "leaf length must be positive"
    malformed

let test_invariants_reject_zero_count_vector () =
  let malformed =
    unsafe_vector
      {
        count = 0;
        root = Raw_empty;
        tail = [||];
        tailoff = 0;
        head = [||];
      }
  in
  check_invariant_failure_contains "zero-count vector"
    "Vector count must be positive" malformed

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
              sizes = Some [| 1; 3 |];
              count = 3;
              height = 2;
            };
        tail = [||];
        tailoff = 3;
        head = [||];
      }
  in
  check_invariant_failure_contains "child height mismatch"
    "child height must equal branch height - 1" malformed

let test_scala_quick_invariants_allow_locally_sparse_nodes () =
  let sparse =
    raw_vector (raw_branch (Array.init rrb_width (fun _ -> raw_leaf 1)))
  in
  check_invariants "Scala Quick locally sparse node" sparse

let test_invariants_reject_linear_height_degradation () =
  let rec skinny_chain height =
    if height = 0 then raw_leaf 1
    else
      Raw_branch
        {
          children = [| skinny_chain (height - 1) |];
          sizes = None;
          count = 1;
          height;
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
              sizes = Some [| 1; 2 |];
              count = 2;
              height = root_height;
            };
        tail = [||];
        tailoff = 2;
        head = [||];
      }
  in
  check_invariant_failure_contains "height bound" "height bound" malformed

let test_size_table_lookup_starts_from_radix_slot () =
  let root =
    Raw_branch
      {
        children =
          [|
            Raw_leaf [| 0 |];
            Raw_leaf [| 1 |];
            Raw_leaf [| 2 |];
            Raw_leaf [| 3 |];
          |];
        sizes = Some [| 96; 97; 96; 97 |];
        count = 97;
        height = 1;
      }
  in
  let values = raw_vector root in
  check_int "size table lookup from radix slot" 3 (nth values 96)

let test_push_get_and_persistence () =
  List.iter
    (fun size ->
      let v = of_list (range size) in
      check_invariants "of_list vector" v;
      check_int "length" size (length v);
      check_list "to_list" (range size) (to_list v);
      for i = 0 to size - 1 do
        check_int "nth" i (nth v i)
      done)
    [ 1; 31; 32; 33; 1023; 1024; 1025 ];
  let v0 = of_list [ 1; 2; 3 ] in
  let v1 = push_back v0 4 in
  check_list "old vector after push" [ 1; 2; 3 ] (to_list v0);
  check_list "new vector after push" [ 1; 2; 3; 4 ] (to_list v1)

let test_nth_tail_read_allocation_does_not_allocate_options () =
  let size = rrb_width in
  let reads = 200_000 in
  let values = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let sum = ref 0 in
  for i = 0 to reads - 1 do
    let index = i mod size in
    sum := !sum + nth values index
  done;
  let allocated = Gc.allocated_bytes () -. before in
  check "nth tail read sum is used" (!sum > 0);
  check_allocated_less_than "nth tail read allocation" 500_000. allocated

let test_strict_peek_reads_do_not_allocate_options () =
  let reads = 200_000 in
  let values = singleton 42 in
  let check_read name expected read =
    Gc.compact ();
    let before = Gc.allocated_bytes () in
    let sum = ref 0 in
    for _ = 1 to reads do
      sum := !sum + read values
    done;
    let allocated = Gc.allocated_bytes () -. before in
    check_int (name ^ " sum") (expected * reads) !sum;
    check_allocated_less_than (name ^ " allocation") 500_000. allocated
  in
  check_read "peek_front" 42 Rrbvec.peek_front;
  check_read "peek_back" 42 Rrbvec.peek_back

let test_set_pop_and_peek () =
  let v0 = of_list (range 1050) in
  let v1 = set v0 10 10010 in
  let v2 = set v1 1049 11049 in
  check_int "old value preserved" 10 (nth v0 10);
  check_int "updated trie value" 10010 (nth v2 10);
  check_int "updated last value" 11049 (nth v2 1049);
  check_raises_invalid_arg "nth at count" (fun () -> ignore (Rrbvec.nth v2 1050));
  expect_none "nth_opt at count" (Rrbvec.nth_opt v2 1050);
  check_raises_invalid_arg "set at count" (fun () -> ignore (set v2 1050 21050));
  check_list "pop removes last"
    (list_slice (to_list v2) 0 (length v2 - 1))
    (to_list (snd (pop_back v2)));
  check_raises_invalid_arg "negative set" (fun () -> ignore (set v0 (-1) 1));
  check_raises_invalid_arg "past end set" (fun () -> ignore (set v0 1051 1))

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
  check_list "prepend_array" [ 1; 2; 3; 4 ]
    (to_list (prepend_array (of_list [ 3; 4 ]) [| 1; 2 |]));
  expect_none "pop_front empty" (Rrbvec.pop_front empty);
  expect_none "pop_back empty" (Rrbvec.pop_back empty);
  expect_none "peek_front_opt empty" (Rrbvec.peek_front_opt empty);
  expect_none "peek_back_opt empty" (Rrbvec.peek_back_opt empty);
  check_raises_invalid_arg "peek_front empty" (fun () ->
      ignore (Rrbvec.peek_front empty));
  check_raises_invalid_arg "peek_back empty" (fun () ->
      ignore (Rrbvec.peek_back empty))

let test_singleton_and_peek_apis () =
  let one = singleton 42 in
  check_invariants "singleton" one;
  check_int "singleton length" 1 (length one);
  check_list "singleton contents" [ 42 ] (to_list one);
  check_int "singleton peek_front" 42 (Rrbvec.peek_front one);
  check_int "singleton peek_back" 42 (Rrbvec.peek_back one);
  Alcotest.(check (option int))
    "singleton peek_front_opt" (Some 42) (Rrbvec.peek_front_opt one);
  Alcotest.(check (option int))
    "singleton peek_back_opt" (Some 42) (Rrbvec.peek_back_opt one);
  let deep = of_list (range 1050) in
  check_int "deep peek_front" 0 (Rrbvec.peek_front deep);
  check_int "deep peek_back" 1049 (Rrbvec.peek_back deep);
  Alcotest.(check (option int))
    "deep peek_front_opt" (Some 0) (Rrbvec.peek_front_opt deep);
  Alcotest.(check (option int))
    "deep peek_back_opt" (Some 1049) (Rrbvec.peek_back_opt deep)

let test_seq_conversions () =
  let empty_from_seq = of_seq Seq.empty in
  check_invariants "of_seq empty" empty_from_seq;
  check "of_seq empty result" (is_empty empty_from_seq);
  check_list "to_seq empty" [] (List.of_seq (to_seq empty));
  let values = range 2049 in
  let visited = ref [] in
  let source =
    values
    |> List.to_seq
    |> Seq.map (fun value ->
           visited := value :: !visited;
           value)
  in
  let vector = of_seq source in
  check_invariants "of_seq" vector;
  check_list "of_seq order" values (to_list vector);
  check_list "of_seq visits once in order" values (List.rev !visited);
  let sequence = to_seq vector in
  check_list "to_seq order" values (List.of_seq sequence);
  check_list "to_seq reusable" values (List.of_seq sequence);
  let first_tail =
    match sequence () with
    | Seq.Nil -> Alcotest.fail "to_seq expected a first value"
    | Seq.Cons (value, tail) ->
        check_int "to_seq first value" 0 value;
        tail
  in
  let check_second name =
    match first_tail () with
    | Seq.Nil -> Alcotest.failf "%s: expected a second value" name
    | Seq.Cons (value, _) -> check_int name 1 value
  in
  check_second "to_seq persistent tail first read";
  check_second "to_seq persistent tail second read";
  let edged =
    concat
      (push_front (of_list (range 1100)) (-1))
      (of_list (List.init 1100 (fun index -> index + 1100)))
    |> fun vector -> subvec vector 17 2183
  in
  check_list "to_seq head root tail and relaxed nodes" (to_list edged)
    (List.of_seq (to_seq edged));
  List.iter
    (fun size ->
      let expected = range size in
      let vector = of_seq (List.to_seq expected) in
      check_invariants "of_seq chunk boundary" vector;
      check_list "of_seq chunk boundary order" expected (to_list vector))
    [ 0; 1; 31; 32; 33; 63; 64; 65; 1023; 1024; 1025 ];
  let large_size = 100_000 in
  let next_value = ref 0 in
  let rec large_source () =
    if !next_value = large_size then Seq.Nil
    else
      let value = !next_value in
      incr next_value;
      Seq.Cons (value, large_source)
  in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let large = of_seq large_source in
  let of_seq_allocated = Gc.allocated_bytes () -. before in
  check_invariants "large of_seq" large;
  check_int "large of_seq source consumed once" large_size !next_value;
  check_int "large of_seq length" large_size (length large);
  check_allocated_less_than "chunked of_seq allocation" 8_000_000.
    of_seq_allocated;
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let sum = Seq.fold_left ( + ) 0 (to_seq large) in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "large to_seq sum" ((large_size * (large_size - 1)) / 2) sum;
  check_allocated_less_than "leaf-based to_seq allocation" 9_000_000.
    allocated

let test_pop_back_head_only_vector () =
  let values = push_front empty 42 in
  check_invariants "head only setup" values;
  check_int "head only setup head length" 1 (header_head_length values);
  check_int "head only setup tail length" 0 (header_tail_length values);
  let value, popped = pop_back values in
  check_int "head only pop_back value" 42 value;
  check_invariants "head only pop_back" popped;
  check "head only pop_back empty" (is_empty popped);
  check_list "head only pop_back order" [] (to_list popped);
  let pushed = push_back popped 7 in
  check_invariants "push after head only pop_back" pushed;
  check_list "push after head only pop_back order" [ 7 ] (to_list pushed)

let list_set values index value =
  List.mapi (fun i current -> if i = index then value else current) values

let list_drop_last values =
  match List.rev values with
  | [] -> invalid_arg "empty list"
  | _ :: rest -> List.rev rest

let test_write_operations_keep_all_historical_versions_persistent () =
  let snapshots = ref [] in
  let remember name v expected =
    check_invariants name v;
    snapshots := (name, v, expected) :: !snapshots;
    v
  in
  let check_history stage =
    List.iter
      (fun (name, v, expected) ->
        check_list (stage ^ ": " ^ name) expected (to_list v))
      !snapshots
  in
  let v0 = remember "empty" empty [] in
  let base_values = range 1100 in
  let v1 =
    List.fold_left (fun acc value -> push_back acc value) v0 base_values
    |> fun v -> remember "after repeated push_back" v base_values
  in
  let front_values = List.init 70 (fun i -> -1 - i) in
  let v2 =
    List.fold_left (fun acc value -> push_front acc value) v1 front_values
  in
  let expected2 = List.rev front_values @ base_values in
  let v2 = remember "after repeated push_front" v2 expected2 in
  let expected3 = list_set expected2 0 9000 in
  let v3 = remember "after set head" (set v2 0 9000) expected3 in
  let expected4 = list_set expected3 80 9080 in
  let v4 = remember "after set root" (set v3 80 9080) expected4 in
  let tail_index = length v4 - 1 in
  let expected5 = list_set expected4 tail_index 9999 in
  let v5 = remember "after set tail" (set v4 tail_index 9999) expected5 in
  check_raises_invalid_arg "set at count in scenario" (fun () ->
      ignore (set v5 (length v5) 10000));
  let expected6 = expected5 @ [ 10000 ] in
  let v6 = remember "after push_back" (push_back v5 10000) expected6 in
  let expected7 = expected6 @ [ 10001; 10002; 10003 ] in
  let v7 =
    remember "after append_list"
      (append_list v6 [ 10001; 10002; 10003 ])
      expected7
  in
  let appended = [| 10004; 10005; 10006 |] in
  let v8 = append_array v7 appended in
  appended.(0) <- -10004;
  let expected8 = expected7 @ [ 10004; 10005; 10006 ] in
  let v8 = remember "after append_array" v8 expected8 in
  let expected9 = [ -103; -102; -101 ] @ expected8 in
  let v9 =
    remember "after prepend_list"
      (prepend_list v8 [ -103; -102; -101 ])
      expected9
  in
  let prepended = [| -106; -105; -104 |] in
  let v10 = prepend_array v9 prepended in
  prepended.(0) <- 106;
  let expected10 = [ -106; -105; -104 ] @ expected9 in
  let v10 = remember "after prepend_array" v10 expected10 in
  let v11 = concat (subvec v10 0 40) (subvec v10 40 (length v10)) in
  let v11 = remember "after concat of subvecs" v11 expected10 in
  let expected12 = expected10 @ [ 20000 ] in
  let v12 = remember "after push_back concat" (push_back v11 20000) expected12 in
  let expected13 = -20000 :: expected12 in
  let v13 = remember "after push_front concat" (push_front v12 (-20000)) expected13 in
  let back, v14 = pop_back v13 in
  check_int "pop_back value after history writes" 20000 back;
  let expected14 = list_drop_last expected13 in
  let v14 = remember "after pop_back" v14 expected14 in
  let front, v15 = pop_front v14 in
  check_int "pop_front value after history writes" (-20000) front;
  let expected15 = List.tl expected14 in
  ignore (remember "after pop_front" v15 expected15);
  check_history "final history check"

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
  expect_none "subvec negative start" (Rrbvec.subvec combined (-1) 2);
  expect_none "subvec inverted range" (Rrbvec.subvec combined 2 1);
  expect_none "subvec past end" (Rrbvec.subvec combined 0 1121)

let test_count_growth_rejects_max_int_length () =
  let rec double remaining values =
    if remaining = 0 then values
    else double (remaining - 1) (concat values values)
  in
  let half = double (Sys.int_size - 2) (singleton 7) in
  let half_length = length half in
  check_int "shared half length" (1 lsl (Sys.int_size - 2)) half_length;
  let half_minus_one = subvec half 0 (half_length - 1) in
  check_raises_invalid_arg "concat rejects max_int length" (fun () ->
      concat half half_minus_one);
  check_raises_invalid_arg "concat rejects overflowed length" (fun () ->
      concat half half);
  let half_minus_two = subvec half 0 (half_length - 2) in
  let largest = concat half half_minus_two in
  check_int "largest supported length" (max_int - 1) (length largest);
  check_raises_invalid_arg "push_back rejects max_int length" (fun () ->
      push_back largest 8);
  check_raises_invalid_arg "push_front rejects max_int length" (fun () ->
      push_front largest 8)

let concat_49_chunks_of_65 () =
  List.init 49 (fun chunk ->
      Rrbvec.init 65 (fun index -> (chunk * 65) + index))

let concat_49_by_65_expected = Array.init 3185 Fun.id

let concat_49_by_65_indices = [ 0; 31; 32; 64; 65; 1592; 3120; 3184 ]

let test_concat_left_associated_49_chunks_of_65_preserves_invariants_and_order () =
  let chunks = concat_49_chunks_of_65 () in
  let combined =
    match chunks with
    | [] -> Alcotest.fail "expected concat chunks"
    | first :: rest -> List.fold_left concat first rest
  in
  check_int_vector "left-associated concat 49 chunks of 65"
    ~indices:concat_49_by_65_indices concat_49_by_65_expected combined

let test_concat_right_associated_49_chunks_of_65_preserves_invariants_and_order () =
  let rec concat_right = function
    | [] -> empty
    | [ values ] -> values
    | values :: rest -> concat values (concat_right rest)
  in
  check_int_vector "right-associated concat 49 chunks of 65"
    ~indices:concat_49_by_65_indices concat_49_by_65_expected
    (concat_right (concat_49_chunks_of_65 ()))

let concat_radix_boundaries =
  [ 0; 1; 31; 32; 33; 63; 64; 65; 1023; 1024; 1025 ]

let test_concat_all_radix_boundary_pairs_preserve_invariants () =
  List.iter
    (fun left_length ->
      List.iter
        (fun right_length ->
          let case_name =
            Printf.sprintf "concat radix boundaries %d + %d" left_length
              right_length
          in
          let left = Rrbvec.init left_length Fun.id in
          let right =
            Rrbvec.init right_length (fun index -> left_length + index)
          in
          let combined = concat left right in
          if left_length = 0 then
            check (case_name ^ " left identity") (combined == right);
          if right_length = 0 then
            check (case_name ^ " right identity") (combined == left);
          check_int_vector case_name
            (Array.init (left_length + right_length) Fun.id)
            combined)
        concat_radix_boundaries)
    concat_radix_boundaries

let test_concat_same_height_trees_uses_at_most_one_new_root_level () =
  let length = 1025 in
  let left = Rrbvec.init length Fun.id in
  let right = Rrbvec.init length (fun index -> length + index) in
  check_int "same-height setup" (internal_height left) (internal_height right);
  let combined = concat left right in
  check_int_vector "same-height concat" (Array.init (2 * length) Fun.id)
    combined;
  check_concat_height_bound "same-height concat root bound" left right combined

let test_concat_short_left_with_tall_right_preserves_height_bound () =
  let left_length = 65 in
  let right_length = 32769 in
  let left = Rrbvec.init left_length Fun.id in
  let right =
    Rrbvec.init right_length (fun index -> left_length + index)
  in
  check "short-left setup has unequal heights"
    (internal_height left < internal_height right);
  let combined = concat left right in
  check_int_vector "short-left tall-right concat"
    (Array.init (left_length + right_length) Fun.id)
    combined;
  check_concat_height_bound "short-left tall-right root bound" left right
    combined

let test_concat_tall_left_with_short_right_preserves_height_bound () =
  let left_length = 32769 in
  let right_length = 65 in
  let left = Rrbvec.init left_length Fun.id in
  let right =
    Rrbvec.init right_length (fun index -> left_length + index)
  in
  check "tall-left setup has unequal heights"
    (internal_height left > internal_height right);
  let combined = concat left right in
  check_int_vector "tall-left short-right concat"
    (Array.init (left_length + right_length) Fun.id)
    combined;
  check_concat_height_bound "tall-left short-right root bound" left right
    combined

let test_concat_does_not_promote_when_final_forest_has_one_node () =
  let left = Rrbvec.init 32 Fun.id in
  let right = Rrbvec.init 1 (fun _ -> 32) in
  let combined = concat left right in
  check_int_vector "single-node final forest" (Array.init 33 Fun.id) combined;
  check_int "single-node final forest root height" 0 (internal_height combined);
  check_concat_height_bound "single-node final forest root bound" left right
    combined

let test_concat_promotes_once_when_final_forest_has_multiple_nodes () =
  let left = Rrbvec.init 64 Fun.id in
  let right = Rrbvec.init 1 (fun _ -> 64) in
  let combined = concat left right in
  check_int_vector "multi-node final forest" (Array.init 65 Fun.id) combined;
  check_int "multi-node final forest root height" 1 (internal_height combined);
  check_concat_height_bound "multi-node final forest root bound" left right
    combined

let test_concat_preserves_left_head_and_right_tail_identity () =
  let left = push_front (Rrbvec.init 65 (fun index -> index + 1)) 0 in
  let right = Rrbvec.init 70 (fun index -> 66 + index) in
  let left_head = header_head_array left in
  let right_tail = header_tail_array right in
  let combined = concat left right in
  check_int_vector "concat outer edge identity" (Array.init 136 Fun.id)
    combined;
  check_same_array "concat preserves left head identity" left_head
    (header_head_array combined);
  check_same_array "concat preserves right tail identity" right_tail
    (header_tail_array combined)

let test_concat_internalizes_left_tail_and_right_head_through_quick_rebalance () =
  let check_case name left right =
    let left_head = header_head_array left in
    let right_tail = header_tail_array right in
    let expected = Array.of_list (to_list left @ to_list right) in
    let combined = concat left right in
    check_int_vector name expected combined;
    check_same_array (name ^ " left head identity") left_head
      (header_head_array combined);
    check_same_array (name ^ " right tail identity") right_tail
      (header_tail_array combined)
  in
  let partial_left = Rrbvec.init 8 Fun.id in
  let partial_right =
    List.fold_right
      (fun value values -> push_front values value)
      (List.init 8 (fun index -> 1000 + index))
      (Rrbvec.init 1 (fun _ -> 1008))
  in
  check_case "partial internalized edges" partial_left partial_right;
  let full_left = Rrbvec.init 32 Fun.id in
  let full_right =
    List.fold_right
      (fun value values -> push_front values value)
      (List.init 32 (fun index -> 1000 + index))
      (Rrbvec.init 1 (fun _ -> 1032))
  in
  check_case "full internalized edges" full_left full_right;
  let absent_left = push_front empty 0 in
  let absent_right = Rrbvec.init 1 (fun _ -> 1) in
  check_case "absent internalized edges" absent_left absent_right

let test_concat_exact_divisible_slot_totals_follow_scala_quick_bound () =
  let check_case ?root_children name left right expected_length =
    check_invariants (name ^ " left setup") left;
    check_invariants (name ^ " right setup") right;
    let combined = concat left right in
    check_int_vector name (Array.init expected_length Fun.id) combined;
    Option.iter
      (fun expected ->
        check_int (name ^ " root child count") expected
          (root_child_count combined))
      root_children
  in
  let next_value = ref 0 in
  let left = raw_vector (raw_branch_of_leaf_lengths next_value [ 1; 1; 14 ]) in
  let right = raw_vector (raw_branch_of_leaf_lengths next_value [ 14; 2 ]) in
  check_int "exact 32 fixture length" 32 !next_value;
  check_case ~root_children:4 "exact 32 logical slots" left right !next_value;
  let next_value = ref 0 in
  let left = raw_vector (raw_branch_of_leaf_lengths next_value [ 8; 8; 16 ]) in
  let right =
    raw_vector (raw_branch_of_leaf_lengths next_value [ 16; 8; 8 ])
  in
  check_int "exact 64 fixture length" 64 !next_value;
  check_case ~root_children:5 "exact 64 logical slots" left right !next_value;
  let next_value = ref 0 in
  let arities = Array.init 35 (fun index -> if index < 9 then 30 else 29) in
  let make_height_one arity =
    raw_branch_of_full_leaves next_value arity
  in
  let left_children = Array.init 17 (fun index -> make_height_one arities.(index)) in
  let right_children =
    Array.init 18 (fun index -> make_height_one arities.(index + 17))
  in
  let left = raw_vector (raw_branch left_children) in
  let right = raw_vector (raw_branch right_children) in
  check_int "exact 1024 logical-slot fixture length" (1024 * rrb_width)
    !next_value;
  check_case "exact 1024 logical slots" left right !next_value

let test_balanced_pairwise_concat_preserves_invariants_for_sparse_boundaries () =
  let chunk_sizes =
    [
      0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 32; 32; 48; 33;
      31; 0; 107; 123; 32; 114; 32; 65; 65; 33; 65; 116; 65; 21; 12; 33;
      1023; 0;
    ]
  in
  let next_value = ref 0 in
  let chunks =
    List.map
      (fun length ->
        let start = !next_value in
        next_value := start + length;
        Rrbvec.init length (fun index -> start + index))
      chunk_sizes
  in
  let rec reduce = function
    | [] -> empty
    | [ values ] -> values
    | values ->
        let rec pass acc = function
          | left :: right :: rest ->
              let combined = concat left right in
              check_invariants "balanced pairwise intermediate" combined;
              pass (combined :: acc) rest
          | [ unpaired ] -> List.rev (unpaired :: acc)
          | [] -> List.rev acc
        in
        reduce (pass [] values)
  in
  let combined = reduce chunks in
  check_int_vector "balanced pairwise sparse boundaries"
    (Array.init !next_value Fun.id) combined

let test_concat_after_subvec_preserves_invariants_and_order () =
  let left_source = Rrbvec.init 1100 Fun.id in
  let right_source = Rrbvec.init 1100 (fun index -> 2000 + index) in
  let left = subvec left_source 17 1083 in
  let right = subvec right_source 13 1091 in
  let expected = Array.of_list (to_list left @ to_list right) in
  check_int_vector "concat after partial-leaf subvec" expected
    (concat left right)

let test_subvec_after_pairwise_concat_preserves_order () =
  let combined = pairwise_concat (concat_49_chunks_of_65 ()) in
  check_int_vector "pairwise source before subvec" concat_49_by_65_expected
    combined;
  let cases =
    [
      ("crosses first chunk boundary", 31, 99);
      ("crosses pairwise concat boundary", 63, 132);
      ("crosses middle concat boundary", 1560, 1625);
      ("crosses right middle boundary", 3050, 3140);
      ("crosses final tail", 3150, 3185);
    ]
  in
  List.iter
    (fun (name, start, stop) ->
      let slice = subvec combined start stop in
      check_int_vector name
        (Array.sub concat_49_by_65_expected start (stop - start))
        slice)
    cases

let test_alternating_concat_and_subvec_preserve_invariants_and_order () =
  let check_step name expected values =
    check_int_vector name (Array.of_list expected) values;
    (values, expected)
  in
  let left = Rrbvec.init 65 Fun.id in
  let right = Rrbvec.init 65 (fun index -> 65 + index) in
  let values, expected =
    check_step "alternating initial concat" (range 130)
      (concat left right)
  in
  let values = subvec values 17 113 in
  let expected = list_slice expected 17 113 in
  let values, expected = check_step "alternating first subvec" expected values in
  let suffix = Rrbvec.init 1025 (fun index -> 1000 + index) in
  let suffix_values = to_list suffix in
  let values, expected =
    check_step "alternating tall suffix concat"
      (expected @ suffix_values)
      (concat values suffix)
  in
  let values = subvec values 31 (List.length expected - 9) in
  let expected = list_slice expected 31 (List.length expected - 9) in
  let values, expected = check_step "alternating second subvec" expected values in
  let empty_slice = subvec values 40 40 in
  ignore (check_step "alternating empty subvec" [] empty_slice);
  let values, expected =
    check_step "alternating empty concat identity" expected
      (concat empty_slice values)
  in
  let prefix = Rrbvec.init 33 (fun index -> -33 + index) in
  let values, expected =
    check_step "alternating partial prefix concat"
      (to_list prefix @ expected)
      (concat prefix values)
  in
  let values = subvec values 1 (List.length expected - 1) in
  let expected = list_slice expected 1 (List.length expected - 1) in
  ignore (check_step "alternating final subvec" expected values)

let concat_map_boundary_values value =
  match non_negative_mod value 4 with
  | 0 -> empty
  | 1 -> singleton (value * 1000)
  | 2 -> Rrbvec.init 32 (fun index -> (value * 1000) + index)
  | _ -> Rrbvec.init 65 (fun index -> (value * 1000) + index)

let list_concat_map_boundary_values values =
  List.concat_map
    (fun value -> to_list (concat_map_boundary_values value))
    values

let test_repeated_concat_map_preserves_invariants_and_order () =
  let rec apply round values expected =
    if round = 0 then ()
    else
      let values = concat_map concat_map_boundary_values values in
      let expected = list_concat_map_boundary_values expected in
      check_int_vector
        (Printf.sprintf "repeated concat_map round %d" (3 - round))
        (Array.of_list expected) values;
      apply (round - 1) values expected
  in
  apply 2 (of_list [ 0; 1; 2; 3 ]) [ 0; 1; 2; 3 ]

let test_concat_aliases_and_collection_helpers_preserve_invariants () =
  let boundaries = [ 0; 1; 31; 32; 33; 63; 64; 65 ] in
  List.iter
    (fun left_length ->
      List.iter
        (fun right_length ->
          let left = Rrbvec.init left_length Fun.id in
          let right_values =
            List.init right_length (fun index -> left_length + index)
          in
          let right = of_list right_values in
          let expected = Array.init (left_length + right_length) Fun.id in
          check_int_vector "concat alias" expected (concat left right);
          check_int_vector "append alias" expected (append left right);
          check_int_vector "prepend alias" expected (prepend left right);
          check_int_vector "append_list helper" expected
            (append_list left right_values);
          let right_array = Array.of_list right_values in
          let appended = append_array left right_array in
          Array.fill right_array 0 (Array.length right_array) (-1);
          check_int_vector "append_array copies input" expected appended;
          let left_values = range left_length in
          let right =
            Rrbvec.init right_length (fun index -> left_length + index)
          in
          check_int_vector "prepend_list helper" expected
            (prepend_list right left_values);
          let left_array = Array.of_list left_values in
          let prepended = prepend_array right left_array in
          Array.fill left_array 0 (Array.length left_array) (-1);
          check_int_vector "prepend_array copies input" expected prepended)
        boundaries)
    boundaries

let test_concat_small_right_preserves_right_tail_segment () =
  let left =
    of_array (Array.init 64 Fun.id)
    |> fun values ->
    List.fold_left push_back values (List.init 9 (fun i -> 64 + i))
  in
  let right = of_array (Array.init 12 (fun i -> 1_000 + i)) in
  let right_tail = header_tail_array right in
  let combined = concat left right in
  check_invariants "concat small right preserves right tail" combined;
  check_int "concat small right tail length" 12 (header_tail_length combined);
  check_list "concat small right order" (to_list left @ to_list right)
    (to_list combined);
  check_same_array "concat small right tail identity" right_tail
    (header_tail_array combined)

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

let test_subvec_whole_range_reuses_vector () =
  let values = of_array (Array.init 10_000 Fun.id) in
  let slice = subvec values 0 (length values) in
  check "whole subvec reuses vector" (slice == values)

let measure_repeated_subvec_allocation ~iterations values start stop =
  let last = ref empty in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  for _ = 1 to iterations do
    last := subvec values start stop
  done;
  let allocated = Gc.allocated_bytes () -. before in
  check_invariants "repeated subvec allocation result" !last;
  allocated

let test_subvec_multi_child_slice_avoids_intermediate_collection_allocation () =
  let size = 100_000 in
  let values = of_array (Array.init size Fun.id) in
  let allocated =
    measure_repeated_subvec_allocation ~iterations:200 values 17 (size - 7)
  in
  check_allocated_less_than "multi-child subvec allocation" 500_000. allocated

let test_subvec_root_only_slice_extracts_edges_during_slicing () =
  let size = 100_000 in
  let values = of_array (Array.init size Fun.id) in
  let allocated =
    measure_repeated_subvec_allocation ~iterations:200 values 17 (size - 64)
  in
  check_allocated_less_than "root-only subvec allocation" 550_000. allocated

let test_subvec_collapses_promoted_singleton_root () =
  let promoted =
    concat (of_list [ 0 ]) (of_array (Array.init 1024 (fun i -> i + 1)))
  in
  check_invariants "promoted concat" promoted;
  let slice = subvec promoted 0 1 in
  check_invariants "singleton root subvec" slice;
  check_list "singleton root subvec order" [ 0 ] (to_list slice)

let test_subvec_collapses_concat_boundary_root () =
  let values =
    Rrbvec.init 31 Fun.id
    |> fun values -> push_front values 0
    |> fun values -> push_front values 0
    |> fun values -> push_front values 0
    |> fun values -> subvec values 29 34
    |> fun values -> push_front values 0
    |> fun values -> concat (Rrbvec.init 1024 Fun.id) values
    |> fun values -> concat (Rrbvec.init 31 Fun.id) values
    |> fun values -> concat values (singleton 0)
  in
  let slice = subvec values 1054 1062 in
  check_invariants "concat boundary subvec" slice;
  check_list "concat boundary subvec order"
    (list_slice (to_list values) 1054 1062)
    (to_list slice)

let test_subvec_collapses_selected_internal_singleton_root () =
  let values =
    Rrbvec.init 31 Fun.id
    |> fun values -> concat values empty
    |> fun values -> subvec values 25 31
    |> fun values -> subvec values 0 6
    |> fun values -> push_front values 0
    |> fun values -> concat (Rrbvec.init 64 Fun.id) values
    |> fun values -> push_front values 0
    |> fun values -> concat (Rrbvec.init 56 Fun.id) values
    |> fun values -> concat (Rrbvec.init 31 Fun.id) values
    |> fun values -> concat values (Rrbvec.init 1023 Fun.id)
    |> fun values -> concat (Rrbvec.init 93 Fun.id) values
    |> fun values -> snd (pop_front values)
    |> fun values -> push_front values 0
    |> fun values -> concat (Rrbvec.init 1 Fun.id) values
  in
  let slice = subvec values 957 990 in
  check_invariants "selected internal singleton root" slice;
  check_list "selected internal singleton root order"
    (list_slice (to_list values) 957 990)
    (to_list slice)

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
  check_int "deep concat first" 0 (nth combined 0);
  check_int "deep concat middle" (size / 2) (nth combined (size / 2));
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

let test_repeated_chunk_concat_satisfies_quick_height_bound () =
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
  check_int "repeated chunk concat first" 0 (nth combined 0);
  check_int "repeated chunk concat last" (size - 1) (peek_back combined);
  check_int "repeated chunk concat sum" ((size * (size - 1)) / 2)
    (fold_left ( + ) 0 combined)

let quick_rebalance_sparse_center_fixture () =
  let full_leaf_count = 8 in
  let sparse_leaf_count = 2 in
  let next_value = ref 0 in
  let leaf length =
    let start = !next_value in
    next_value := start + length;
    raw_leaf_range start length
  in
  let left_children =
    Array.init
      (full_leaf_count + sparse_leaf_count)
      (fun index -> if index < full_leaf_count then leaf rrb_width else leaf 1)
  in
  let right_children =
    Array.init
      (sparse_leaf_count + full_leaf_count)
      (fun index -> if index < sparse_leaf_count then leaf 1 else leaf rrb_width)
  in
  ( raw_vector (raw_branch left_children),
    raw_vector (raw_branch right_children),
    !next_value,
    Array.sub left_children 0 full_leaf_count,
    Array.sub right_children sparse_leaf_count full_leaf_count )

let test_quick_rebalance_reuses_unchanged_full_prefix_and_suffix_nodes () =
  let left, right, expected_length, left_prefix, right_suffix =
    quick_rebalance_sparse_center_fixture ()
  in
  check_invariants "sparse middle concat left setup" left;
  check_invariants "sparse middle concat right setup" right;
  let combined = concat left right in
  check_int_vector "Quick sparse-center sharing"
    (Array.init expected_length Fun.id) combined;
  Array.iteri
    (fun index node ->
      check_node_shared
        (Printf.sprintf "Quick unchanged left prefix node %d" index)
        node combined)
    left_prefix;
  Array.iteri
    (fun index node ->
      check_node_shared
        (Printf.sprintf "Quick unchanged right suffix node %d" index)
        node combined)
    right_suffix

let test_quick_rebalance_allocates_only_boundary_paths_and_changed_nodes () =
  let left, right, expected_length, _, _ =
    quick_rebalance_sparse_center_fixture ()
  in
  check_invariants "Quick allocation left setup" left;
  check_invariants "Quick allocation right setup" right;
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let combined = concat left right in
  let allocated = Gc.allocated_bytes () -. before in
  check_int_vector "Quick boundary-path allocation"
    (Array.init expected_length Fun.id) combined;
  check_allocated_less_than "Quick boundary-path allocation" 20_000. allocated

let test_push_back_same_height_fast_path_allocation () =
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
  check_invariants "push_back same-height allocation" values;
  check_int "push_back same-height length" size (length values);
  check_int "push_back same-height last" (size - 1) (peek_back values);
  check_allocated_less_than "push_back same-height allocation" 4_500_000.
    allocated

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

let test_regular_builds_omit_size_tables () =
  let from_array = of_array (Array.init 20_000 Fun.id) in
  let pushed =
    let rec loop i acc =
      if i = 20_000 then acc else loop (i + 1) (push_back acc i)
    in
    loop 0 empty
  in
  check_invariants "regular of_array" from_array;
  check_invariants "regular push_back" pushed;
  check_int "of_array size tables" 0 (regular_size_table_count from_array);
  check_int "push_back size tables" 0 (regular_size_table_count pushed);
  check_int "of_array radix nth" 12_345 (nth from_array 12_345);
  check_int "push_back radix nth" 12_345 (nth pushed 12_345)

let push_back_range start count values =
  let rec loop i acc =
    if i = count then acc else loop (i + 1) (push_back acc (start + i))
  in
  loop 0 values

let test_of_array_keeps_right_edge_in_tail () =
  let single_leaf = of_array (Array.init rrb_width Fun.id) in
  check_invariants "single leaf of_array" single_leaf;
  check_int "single leaf root height" (-1) (internal_height single_leaf);
  check_int "single leaf tailoff" 0 (header_tailoff single_leaf);
  check_int "single leaf tail length" rrb_width
    (header_tail_length single_leaf);
  let partial = of_array (Array.init (rrb_width + 8) Fun.id) in
  check_invariants "partial right edge of_array" partial;
  check_int "partial right edge tailoff" rrb_width (header_tailoff partial);
  check_int "partial right edge tail length" 8 (header_tail_length partial);
  check_int "partial right edge size tables" 0
    (regular_size_table_count partial);
  let appended = push_back_range (rrb_width + 8) (rrb_width + 1) partial in
  check_invariants "partial right edge append" appended;
  check_int "partial right edge append size tables" 0
    (regular_size_table_count appended);
  check_list "partial right edge append order"
    (range ((2 * rrb_width) + 9))
    (to_list appended);
  let exact = of_array (Array.init (2 * rrb_width) Fun.id) in
  check_invariants "exact leaf multiple of_array" exact;
  check_int "exact leaf multiple tailoff" rrb_width (header_tailoff exact);
  check_int "exact leaf multiple tail length" rrb_width
    (header_tail_length exact);
  check_int "exact leaf multiple size tables" 0
    (regular_size_table_count exact);
  check_list "exact leaf multiple order" (range (2 * rrb_width))
    (to_list exact)

let test_subvec_keeps_right_edge_in_tail () =
  let values = of_array (Array.init (3 * rrb_width) Fun.id) in
  let partial = subvec values 0 (rrb_width + 8) in
  check_invariants "partial right edge subvec" partial;
  check_int "partial right edge subvec tailoff" rrb_width
    (header_tailoff partial);
  check_int "partial right edge subvec tail length" 8
    (header_tail_length partial);
  check_int "partial right edge subvec size tables" 0
    (regular_size_table_count partial);
  let appended = push_back_range (rrb_width + 8) (rrb_width + 1) partial in
  check_invariants "partial right edge subvec append" appended;
  check_int "partial right edge subvec append size tables" 0
    (regular_size_table_count appended);
  check_list "partial right edge subvec append order"
    (range ((2 * rrb_width) + 9))
    (to_list appended);
  let exact = subvec values 0 (2 * rrb_width) in
  check_invariants "exact leaf multiple subvec" exact;
  check_int "exact leaf multiple subvec tailoff" rrb_width
    (header_tailoff exact);
  check_int "exact leaf multiple subvec tail length" rrb_width
    (header_tail_length exact);
  check_int "exact leaf multiple subvec size tables" 0
    (regular_size_table_count exact);
  check_list "exact leaf multiple subvec order" (range (2 * rrb_width))
    (to_list exact)

let test_pop_back_refills_tail_from_root () =
  let values = push_back (of_array (Array.init (3 * rrb_width) Fun.id)) 96 in
  check_invariants "pop back refill setup" values;
  check_int "setup tail length" 1 (header_tail_length values);
  let value, popped = pop_back values in
  check_int "pop back refill value" 96 value;
  check_invariants "pop back refill" popped;
  check_int "pop back refill length" (3 * rrb_width) (length popped);
  check_int "pop back refill tail length" rrb_width
    (header_tail_length popped);
  check_int "pop back refill tailoff" (2 * rrb_width)
    (header_tailoff popped);
  check_list "pop back refill order" (range (3 * rrb_width))
    (to_list popped)

let test_repeated_pop_back_allocation_is_boundary_linear () =
  let size = 5_000 in
  let rec drain values =
    match Rrbvec.pop_back values with
    | None -> values
    | Some (_, remaining) -> drain remaining
  in
  let values = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let result = drain values in
  let allocated = Gc.allocated_bytes () -. before in
  check_invariants "repeated pop_back allocation" result;
  check "repeated pop_back result" (is_empty result);
  check_allocated_less_than "repeated pop_back allocation" 20_000_000.
    allocated

let test_repeated_pop_front_allocation_is_boundary_linear () =
  let size = 5_000 in
  let rec drain values =
    match Rrbvec.pop_front values with
    | None -> values
    | Some (_, remaining) -> drain remaining
  in
  let values = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let result = drain values in
  let allocated = Gc.allocated_bytes () -. before in
  check_invariants "repeated pop_front allocation" result;
  check "repeated pop_front result" (is_empty result);
  check_allocated_less_than "repeated pop_front allocation" 20_000_000.
    allocated

let test_push_front_same_height_fast_path_allocation () =
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
  check_invariants "push_front same-height allocation" values;
  check_int "push_front same-height length" size (length values);
  check_int "push_front same-height first" (size - 1) (peek_front values);
  check_int "push_front same-height last" 0 (peek_back values);
  check_allocated_less_than "push_front same-height allocation" 4_600_000.
    allocated

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

let test_to_list_large_allocation_avoids_intermediate_array () =
  let size = 100_000 in
  let v = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let values = to_list v in
  let allocated = Gc.allocated_bytes () -. before in
  check_int "large to_list length" size (List.length values);
  check_int "large to_list head" 0 (List.hd values);
  check_int "large to_list last" (size - 1) (List.nth values (size - 1));
  check_allocated_less_than "large to_list allocation" 3_000_000. allocated

let test_list_builders_avoid_full_intermediate_array () =
  let size = 100_000 in
  let values = List.init size Fun.id in
  let check_builder name allocation_limit f =
    Gc.compact ();
    let before = Gc.allocated_bytes () in
    let vector = f values in
    let allocated = Gc.allocated_bytes () -. before in
    check_invariants name vector;
    check_int (name ^ " length") size (length vector);
    check_int (name ^ " first") 0 (peek_front vector);
    check_int (name ^ " last") (size - 1) (peek_back vector);
    check_allocated_less_than (name ^ " allocation") allocation_limit allocated
  in
  check_builder "large of_list" 1_030_000. of_list;
  check_builder "large append_list" 1_700_000. (append_list empty);
  check_builder "large prepend_list" 1_700_000. (prepend_list empty)

let test_map_large_allocation_is_leaf_linear () =
  let size = 100_000 in
  let v = of_array (Array.init size Fun.id) in
  Gc.compact ();
  let before = Gc.allocated_bytes () in
  let mapped = map (fun value -> (value * 2) + 1) v in
  let allocated = Gc.allocated_bytes () -. before in
  check_invariants "large map allocation" mapped;
  check_int "large map length" size (length mapped);
  check_int "large map sum" ((2 * (size * (size - 1) / 2)) + size)
    (fold_left ( + ) 0 mapped);
  check_allocated_less_than "large map allocation" 5_000_000. allocated

let test_map_visits_values_in_order () =
  let v = push_front (of_list (range 100)) (-1) in
  let visited = ref [] in
  let mapped =
    map
      (fun value ->
        visited := value :: !visited;
        value + 1)
      v
  in
  check_list "map visit order" (to_list v) (List.rev !visited);
  check_list "map result order" (List.map (( + ) 1) (to_list v))
    (to_list mapped)

let test_conversions_and_map () =
  let values = [| 1; 2; 3 |] in
  let v = of_array values in
  values.(1) <- 99;
  check_array "of_array copies input" [| 1; 2; 3 |] (to_array v);
  let exported = to_array v in
  exported.(2) <- 77;
  check_int "to_array copies output" 3 (nth v 2);
  let mapped = map string_of_int v in
  check_string_list "map type change" [ "1"; "2"; "3" ] (to_list mapped);
  check_list "append_list" (range 70)
    (to_list
       (append_list (of_list (range 31)) (List.init 39 (fun i -> i + 31))));
  check_list "append_array" (range 70)
    (to_list
       (append_array (of_list (range 31)) (Array.init 39 (fun i -> i + 31))))

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
          test_case "invariants_reject_zero_count_vector"
            test_invariants_reject_zero_count_vector;
          test_case "invariants_reject_root_singleton_branch"
            test_invariants_reject_root_singleton_branch;
          test_case "invariants_reject_child_height_mismatch"
            test_invariants_reject_child_height_mismatch;
          test_case "scala_quick_invariants_allow_locally_sparse_nodes"
            test_scala_quick_invariants_allow_locally_sparse_nodes;
          test_case "invariants_reject_linear_height_degradation"
            test_invariants_reject_linear_height_degradation;
          test_case "size_table_lookup_starts_from_radix_slot"
            test_size_table_lookup_starts_from_radix_slot;
          test_case "push_get_and_persistence" test_push_get_and_persistence;
          test_case "count_growth_rejects_max_int_length"
            test_count_growth_rejects_max_int_length;
          test_case "nth_tail_read_allocation_does_not_allocate_options"
            test_nth_tail_read_allocation_does_not_allocate_options;
          test_case "strict_peek_reads_do_not_allocate_options"
            test_strict_peek_reads_do_not_allocate_options;
          test_case "set_pop_and_peek" test_set_pop_and_peek;
          test_case "front_and_back_operations" test_front_and_back_operations;
          test_case "singleton_and_peek_apis" test_singleton_and_peek_apis;
          test_case "pop_back_head_only_vector"
            test_pop_back_head_only_vector;
          test_case "write_operations_keep_all_historical_versions_persistent"
            test_write_operations_keep_all_historical_versions_persistent;
        ] );
      ( "concat-quick",
        [
          test_case
            "concat_left_associated_49_chunks_of_65_preserves_invariants_and_order"
            test_concat_left_associated_49_chunks_of_65_preserves_invariants_and_order;
          test_case
            "concat_right_associated_49_chunks_of_65_preserves_invariants_and_order"
            test_concat_right_associated_49_chunks_of_65_preserves_invariants_and_order;
          test_case "concat_all_radix_boundary_pairs_preserve_invariants"
            test_concat_all_radix_boundary_pairs_preserve_invariants;
          test_case
            "concat_same_height_trees_uses_at_most_one_new_root_level"
            test_concat_same_height_trees_uses_at_most_one_new_root_level;
          test_case "concat_short_left_with_tall_right_preserves_height_bound"
            test_concat_short_left_with_tall_right_preserves_height_bound;
          test_case "concat_tall_left_with_short_right_preserves_height_bound"
            test_concat_tall_left_with_short_right_preserves_height_bound;
          test_case "concat_does_not_promote_when_final_forest_has_one_node"
            test_concat_does_not_promote_when_final_forest_has_one_node;
          test_case "concat_promotes_once_when_final_forest_has_multiple_nodes"
            test_concat_promotes_once_when_final_forest_has_multiple_nodes;
          test_case "concat_preserves_left_head_and_right_tail_identity"
            test_concat_preserves_left_head_and_right_tail_identity;
          test_case
            "concat_internalizes_left_tail_and_right_head_through_quick_rebalance"
            test_concat_internalizes_left_tail_and_right_head_through_quick_rebalance;
          test_case "concat_small_right_preserves_right_tail_segment"
            test_concat_small_right_preserves_right_tail_segment;
          test_case
            "concat_exact_divisible_slot_totals_follow_scala_quick_bound"
            test_concat_exact_divisible_slot_totals_follow_scala_quick_bound;
          test_case
            "balanced_pairwise_concat_preserves_invariants_for_sparse_boundaries"
            test_balanced_pairwise_concat_preserves_invariants_for_sparse_boundaries;
          test_case "concat_after_subvec_preserves_invariants_and_order"
            test_concat_after_subvec_preserves_invariants_and_order;
          test_case "subvec_after_pairwise_concat_preserves_order"
            test_subvec_after_pairwise_concat_preserves_order;
          test_case
            "alternating_concat_and_subvec_preserve_invariants_and_order"
            test_alternating_concat_and_subvec_preserve_invariants_and_order;
          test_case "repeated_concat_map_preserves_invariants_and_order"
            test_repeated_concat_map_preserves_invariants_and_order;
          test_case "concat_aliases_and_collection_helpers_preserve_invariants"
            test_concat_aliases_and_collection_helpers_preserve_invariants;
          test_case
            "quick_rebalance_reuses_unchanged_full_prefix_and_suffix_nodes"
            test_quick_rebalance_reuses_unchanged_full_prefix_and_suffix_nodes;
          test_case
            "quick_rebalance_allocates_only_boundary_paths_and_changed_nodes"
            test_quick_rebalance_allocates_only_boundary_paths_and_changed_nodes;
        ] );
      ( "rrb",
        [
          test_case "concat_and_subvec_preserve_order"
            test_concat_and_subvec_preserve_order;
          test_case "subvec_slices_head_root_and_tail"
            test_subvec_slices_head_root_and_tail;
          test_case "subvec_small_slice_allocation_does_not_scale_with_vector_length"
            test_subvec_small_slice_allocation_does_not_scale_with_vector_length;
          test_case "subvec_whole_range_reuses_vector"
            test_subvec_whole_range_reuses_vector;
          test_case
            "subvec_multi_child_slice_avoids_intermediate_collection_allocation"
            test_subvec_multi_child_slice_avoids_intermediate_collection_allocation;
          test_case "subvec_root_only_slice_extracts_edges_during_slicing"
            test_subvec_root_only_slice_extracts_edges_during_slicing;
          test_case "subvec_collapses_promoted_singleton_root"
            test_subvec_collapses_promoted_singleton_root;
          test_case "subvec_collapses_concat_boundary_root"
            test_subvec_collapses_concat_boundary_root;
          test_case "subvec_collapses_selected_internal_singleton_root"
            test_subvec_collapses_selected_internal_singleton_root;
          test_case "repeated_concat_stays_stack_safe"
            test_repeated_concat_stays_stack_safe;
          test_case "repeated_chunk_concat_satisfies_quick_height_bound"
            test_repeated_chunk_concat_satisfies_quick_height_bound;
          test_case "push_back_same_height_fast_path_allocation"
            test_push_back_same_height_fast_path_allocation;
          test_case "push_keeps_height_logarithmic"
            test_push_keeps_height_logarithmic;
          test_case "regular_builds_omit_size_tables"
            test_regular_builds_omit_size_tables;
          test_case "of_array_keeps_right_edge_in_tail"
            test_of_array_keeps_right_edge_in_tail;
          test_case "subvec_keeps_right_edge_in_tail"
            test_subvec_keeps_right_edge_in_tail;
          test_case "pop_back_refills_tail_from_root"
            test_pop_back_refills_tail_from_root;
          test_case "repeated_pop_back_allocation_is_boundary_linear"
            test_repeated_pop_back_allocation_is_boundary_linear;
          test_case "repeated_pop_front_allocation_is_boundary_linear"
            test_repeated_pop_front_allocation_is_boundary_linear;
          test_case "push_front_same_height_fast_path_allocation"
            test_push_front_same_height_fast_path_allocation;
        ] );
      ( "conversion",
        [
          test_case "conversions_and_map" test_conversions_and_map;
          test_case "seq_conversions" test_seq_conversions;
          test_case "fold_right_visits_values_in_order"
            test_fold_right_visits_values_in_order;
          test_case "fold_right_large_allocation_is_linear"
            test_fold_right_large_allocation_is_linear;
          test_case "to_list_large_allocation_avoids_intermediate_array"
            test_to_list_large_allocation_avoids_intermediate_array;
          test_case "list_builders_avoid_full_intermediate_array"
            test_list_builders_avoid_full_intermediate_array;
          test_case "map_large_allocation_is_leaf_linear"
            test_map_large_allocation_is_leaf_linear;
          test_case "map_visits_values_in_order"
            test_map_visits_values_in_order;
        ] );
    ]
