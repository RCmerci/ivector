let bits = 5
let view_shift = -1
let width = 1 lsl bits
let mask = width - 1
let append_balance_slack = 8
let append_chunk_limit = 1024

type 'a node =
  | Empty
  | Branch of 'a node array
  | Leaf of 'a array
  | View of { base : 'a t; start : int }
  | Append of { left : 'a t; right : 'a t }
and 'a t = {
  count : int;
  shift : int;
  root : 'a node;
  tail : 'a array;
  tailoff : int;
  append_height : int;
  append_leaves : int;
}

let empty =
  {
    count = 0;
    shift = bits;
    root = Empty;
    tail = [||];
    tailoff = 0;
    append_height = 0;
    append_leaves = 1;
  }

let length v = v.count

let is_empty v = v.count = 0

let append_balanced height leaves =
  let excess = height - append_balance_slack in
  excess <= 0
  || (excess < Sys.int_size && leaves > (1 lsl (excess - 1)))

let tailoff count =
  if count < width then 0 else ((count - 1) lsr bits) lsl bits

let invalid_index () = invalid_arg "index out of bounds"

let make_materialized ~count ~shift ~root ~tail ~tailoff =
  { count; shift; root; tail; tailoff; append_height = 0; append_leaves = 1 }

let raw_append left right append_height append_leaves =
  {
    count = left.count + right.count;
    shift = view_shift;
    root = Append { left; right };
    tail = [||];
    tailoff = max_int;
    append_height;
    append_leaves;
  }

let append_metadata left right =
  ( 1 + max left.append_height right.append_height,
    left.append_leaves + right.append_leaves )

let rec array_for_node index level node =
  match node with
  | Leaf values -> values
  | Branch children ->
      array_for_node index (level - bits)
        (Array.unsafe_get children ((index lsr level) land mask))
  | _ -> invalid_arg "corrupt vector"

let rec array_for v index =
  if index < 0 || index >= v.count then invalid_index ();
  if index >= v.tailoff then v.tail
  else array_for_node index v.shift v.root

let rec get_node index level node =
  match node with
  | Leaf values -> Array.unsafe_get values (index land mask)
  | Branch children ->
      get_node index (level - bits)
        (Array.unsafe_get children ((index lsr level) land mask))
  | _ -> invalid_arg "corrupt vector"

let get_shift_10 root index =
  match root with
  | Branch root_children -> (
      match Array.unsafe_get root_children ((index lsr (bits * 2)) land mask) with
      | Branch leaf_parents -> (
          match Array.unsafe_get leaf_parents ((index lsr bits) land mask) with
          | Leaf values -> Array.unsafe_get values (index land mask)
          | child -> get_node index bits child)
      | child -> get_node index bits child)
  | node -> get_node index (bits * 2) node

let rec get v index =
  if index < 0 || index >= v.count then invalid_index ();
  if index >= v.tailoff then Array.unsafe_get v.tail (index land mask)
  else if v.shift = view_shift then
    match v.root with
    | View { base; start } -> get base (start + index)
    | Append { left; right } ->
        if index < left.count then get left index else get right (index - left.count)
    | _ -> invalid_arg "corrupt vector"
  else if v.shift = bits * 2 then get_shift_10 v.root index
  else get_node index v.shift v.root

let rec do_assoc level node index value =
  match node with
  | Branch children ->
      let children' = Array.copy children in
      let i = (index lsr level) land mask in
      Array.unsafe_set children' i
        (do_assoc (level - bits) (Array.unsafe_get children i) index value);
      Branch children'
  | Leaf values ->
      let values' = Array.copy values in
      Array.unsafe_set values' (index land mask) value;
      Leaf values'
  | _ -> invalid_arg "corrupt vector"

let rec new_path level leaf =
  if level = 0 then leaf
  else
    let children = Array.make width Empty in
    Array.unsafe_set children 0 (new_path (level - bits) leaf);
    Branch children

let root_shift_for_tailoff tailoff =
  let leaves = tailoff lsr bits in
  let rec loop shift =
    if leaves <= (1 lsl shift) then shift else loop (shift + bits)
  in
  loop bits

let rec node_of_array_range values start stop level =
  let children = Array.make width Empty in
  let child_span = 1 lsl level in
  for child_index = 0 to width - 1 do
    let child_start = start + (child_index * child_span) in
    if child_start < stop then (
      let child_stop = min stop (child_start + child_span) in
      let child =
        if level = bits then
          Leaf (Array.sub values child_start (child_stop - child_start))
        else node_of_array_range values child_start child_stop (level - bits)
      in
      Array.unsafe_set children child_index child)
  done;
  Branch children

let of_array values =
  let count = Array.length values in
  if count = 0 then empty
  else
    let tail_start = tailoff count in
    let shift = root_shift_for_tailoff tail_start in
    let root =
      if tail_start = 0 then Empty else node_of_array_range values 0 tail_start shift
    in
    let tail = Array.sub values tail_start (count - tail_start) in
    make_materialized ~count ~shift ~root ~tail ~tailoff:tail_start

let blit_materialized_range dst dst_pos v start stop =
  let rec loop index dst_pos =
    if index < stop then (
      let values = array_for v index in
      let offset = index land mask in
      let length = min (Array.length values - offset) (stop - index) in
      Array.blit values offset dst dst_pos length;
      loop (index + length) (dst_pos + length))
  in
  loop start dst_pos

let blit_to_array dst v =
  let first_job = (v, 0, v.count, 0) in
  let stack = ref (Array.make 16 first_job) in
  let stack_length = ref 1 in
  let push value =
    if !stack_length = Array.length !stack then (
      let stack' = Array.make (!stack_length * 2) value in
      Array.blit !stack 0 stack' 0 !stack_length;
      stack := stack');
    Array.unsafe_set !stack !stack_length value;
    incr stack_length
  in
  let pop () =
    decr stack_length;
    Array.unsafe_get !stack !stack_length
  in
  while !stack_length > 0 do
    let v, start, stop, dst_pos = pop () in
    if start <> stop then
      if v.shift <> view_shift then blit_materialized_range dst dst_pos v start stop
      else
        match v.root with
        | View { base; start = base_start } ->
            push (base, base_start + start, base_start + stop, dst_pos)
        | Append { left; right } ->
            if stop <= left.count then push (left, start, stop, dst_pos)
            else if start >= left.count then
              push (right, start - left.count, stop - left.count, dst_pos)
            else (
              let left_length = left.count - start in
              push (right, 0, stop - left.count, dst_pos + left_length);
              push (left, start, left.count, dst_pos))
        | _ -> invalid_arg "corrupt vector"
  done

let to_array v =
  if v.count = 0 then [||]
  else
    let values = Array.make v.count (get v 0) in
    blit_to_array values v;
    values

let rec push_tail count level parent tail_leaf =
  let children =
    match parent with
    | Empty -> Array.make width Empty
    | Branch children -> Array.copy children
    | _ -> invalid_arg "corrupt vector"
  in
  let subidx = ((count - 1) lsr level) land mask in
  let child =
    if level = bits then tail_leaf
    else
      match Array.unsafe_get children subidx with
      | Empty -> new_path (level - bits) tail_leaf
      | child -> push_tail count (level - bits) child tail_leaf
  in
  Array.unsafe_set children subidx child;
  Branch children

let append_tail tail value =
  let length = Array.length tail in
  let tail' = Array.make (length + 1) value in
  Array.blit tail 0 tail' 0 length;
  tail'

let rec push v value =
  if v.shift = view_shift then push (materialize v) value
  else
    let count = v.count + 1 in
    if Array.length v.tail < width then
      { v with count; tail = append_tail v.tail value }
    else
      let tail_leaf = Leaf v.tail in
      let root, shift =
        if (v.count lsr bits) > (1 lsl v.shift) then
          let children = Array.make width Empty in
          Array.unsafe_set children 0 v.root;
          Array.unsafe_set children 1 (new_path v.shift tail_leaf);
          (Branch children, v.shift + bits)
        else (push_tail v.count v.shift v.root tail_leaf, v.shift)
      in
      make_materialized ~count ~shift ~root ~tail:[| value |] ~tailoff:(tailoff count)

and materialize v =
  of_array (to_array v)

let append_materialized_chunk_if_room left right =
  if
    left.shift <> view_shift && right.shift <> view_shift && right.count <= width
    && left.count + right.count <= append_chunk_limit
  then
    let count = left.count + right.count in
    let default =
      if left.count = 0 then Array.unsafe_get right.tail 0 else get left 0
    in
    let values = Array.make count default in
    blit_to_array values left;
    Array.blit right.tail 0 values left.count right.count;
    Some (of_array values)
  else None

let rec collect_append_leaves v acc =
  if v.shift <> view_shift then v :: acc
  else
    match v.root with
    | Append { left; right } ->
        collect_append_leaves left (collect_append_leaves right acc)
    | View _ -> v :: acc
    | _ -> invalid_arg "corrupt vector"

let rec make_append left right =
  if left.count = 0 then right
  else if right.count = 0 then left
  else
    match append_small_to_rightmost left right with
    | Some merged -> merged
    | None ->
        let append_height, append_leaves = append_metadata left right in
        if append_balanced append_height append_leaves then
          raw_append left right append_height append_leaves
        else rebalance_append left right

and append_small_to_rightmost left right =
  if right.shift = view_shift || right.count > width then None
  else if left.shift <> view_shift then append_materialized_chunk_if_room left right
  else
    match left.root with
    | Append { left = left_left; right = left_right } -> (
        match append_small_to_rightmost left_right right with
        | None -> None
        | Some merged_right -> Some (make_append left_left merged_right))
    | View _ -> None
    | _ -> invalid_arg "corrupt vector"

and rebalance_append left right =
  if left.append_height > right.append_height then
    match left.root with
    | Append { left = left_left; right = left_right }
      when left.shift = view_shift ->
        make_append left_left (make_append left_right right)
    | _ -> rebuild_append left right
  else
    match right.root with
    | Append { left = right_left; right = right_right }
      when right.shift = view_shift ->
        make_append (make_append left right_left) right_right
    | _ -> rebuild_append left right

and rebuild_append left right =
  let leaves =
    collect_append_leaves left (collect_append_leaves right []) |> Array.of_list
  in
  let rec build start length =
    if length = 1 then Array.unsafe_get leaves start
    else
      let left_length = length / 2 in
      make_append
        (build start left_length)
        (build (start + left_length) (length - left_length))
  in
  build 0 (Array.length leaves)

let make_view base start count =
  let base, start =
    match base.root with
    | View { base; start = base_start } when base.shift = view_shift ->
        (base, base_start + start)
    | _ -> (base, start)
  in
  {
    count;
    shift = view_shift;
    root = View { base; start };
    tail = [||];
    tailoff = max_int;
    append_height = 0;
    append_leaves = 1;
  }

let rec set v index value =
  if index < 0 || index > v.count then invalid_index ();
  if v.shift = view_shift then set (materialize v) index value
  else if index = v.count then push v value
  else if index >= v.tailoff then (
    let tail = Array.copy v.tail in
    Array.unsafe_set tail (index land mask) value;
    { v with tail })
  else { v with root = do_assoc v.shift v.root index value }

let peek v =
  if v.count = 0 then invalid_index ();
  if v.shift = view_shift then get v (v.count - 1)
  else v.tail.((v.count - 1) land mask)

let rec pop_tail count level node =
  match node with
  | Empty -> None
  | Branch children ->
      let subidx = ((count - 2) lsr level) land mask in
      if level > bits then (
        let child = children.(subidx) in
        match pop_tail count (level - bits) child with
        | None when subidx = 0 -> None
        | new_child ->
            let children' = Array.copy children in
            children'.(subidx) <- Option.value new_child ~default:Empty;
            Some (Branch children'))
      else if subidx = 0 then None
      else
        let children' = Array.copy children in
        children'.(subidx) <- Empty;
        Some (Branch children')
  | _ -> invalid_arg "corrupt vector"

let rec pop v =
  if v.count = 0 then invalid_index ()
  else if v.shift = view_shift then pop (materialize v)
  else if v.count = 1 then empty
  else if Array.length v.tail > 1 then
    let count = v.count - 1 in
    {
      v with
      count;
      tail = Array.sub v.tail 0 (Array.length v.tail - 1);
      tailoff = tailoff count;
    }
  else
    let count = v.count - 1 in
    let new_tail = array_for v (v.count - 2) in
    let root = pop_tail v.count v.shift v.root |> Option.value ~default:Empty in
    let root, shift =
      match root with
      | Branch children when v.shift > bits && children.(1) = Empty -> (
          match children.(0) with
          | Empty -> (Empty, bits)
          | child -> (child, v.shift - bits))
      | _ -> (root, v.shift)
    in
    make_materialized ~count ~shift ~root ~tail:new_tail ~tailoff:(tailoff count)

let fold_array = Array.fold_left

let fold_array_range f acc values start stop =
  let acc = ref acc in
  for i = start to stop - 1 do
    acc := f !acc (Array.unsafe_get values i)
  done;
  !acc

let rec fold_node f acc node =
  match node with
  | Empty -> acc
  | Leaf values -> fold_array f acc values
  | Branch children ->
      let acc = ref acc in
      for i = 0 to width - 1 do
        acc := fold_node f !acc (Array.unsafe_get children i)
      done;
      !acc
  | _ -> invalid_arg "corrupt vector"

let rec fold_range f acc v start stop =
  if start = stop then acc
  else if v.shift = view_shift then
    match v.root with
    | View { base; start = base_start } ->
        fold_range f acc base (base_start + start) (base_start + stop)
    | Append { left; right } ->
        if stop <= left.count then fold_range f acc left start stop
        else if start >= left.count then
          fold_range f acc right (start - left.count) (stop - left.count)
        else
          let acc = fold_range f acc left start left.count in
          fold_range f acc right 0 (stop - left.count)
    | _ -> invalid_arg "corrupt vector"
  else
    let rec loop index acc =
      if index = stop then acc
      else
        let values = array_for v index in
        let offset = index land mask in
        let length = min (Array.length values - offset) (stop - index) in
        loop (index + length) (fold_array_range f acc values offset (offset + length))
    in
    loop start acc

let fold_materialized f acc v =
  let acc = fold_node f acc v.root in
  fold_array f acc v.tail

let append_depth_exceeds v max_depth =
  v.append_height > max_depth

let fold_left_iterative f acc v =
  let stack = ref (Array.make 16 v) in
  let stack_length = ref 1 in
  let push value =
    if !stack_length = Array.length !stack then (
      let stack' = Array.make (!stack_length * 2) value in
      Array.blit !stack 0 stack' 0 !stack_length;
      stack := stack');
    Array.unsafe_set !stack !stack_length value;
    incr stack_length
  in
  let pop () =
    decr stack_length;
    Array.unsafe_get !stack !stack_length
  in
  let acc = ref acc in
  while !stack_length > 0 do
    let v = pop () in
    if v.shift <> view_shift then acc := fold_materialized f !acc v
    else
      match v.root with
      | View { base; start } -> acc := fold_range f !acc base start (start + v.count)
      | Append { left; right } ->
          push right;
          push left
      | _ -> invalid_arg "corrupt vector"
  done;
  !acc

let rec fold_left_recursive f acc v =
  if v.shift <> view_shift then fold_materialized f acc v
  else
    match v.root with
    | View { base; start } -> fold_range f acc base start (start + v.count)
    | Append { left; right } -> fold_left_recursive f (fold_left_recursive f acc left) right
    | _ -> invalid_arg "corrupt vector"

let fold_left f acc v =
  if v.count > 128_000 && append_depth_exceeds v 128_000 then
    fold_left_iterative f acc v
  else fold_left_recursive f acc v

let map f v = fold_left (fun acc value -> push acc (f value)) empty v

let subvec v start stop =
  if start < 0 || stop < start || stop > v.count then invalid_index ();
  let count = stop - start in
  make_view v start count

let concat left right = make_append left right

let of_list values = of_array (Array.of_list values)

let append_array v values =
  if Array.length values = 0 then v else make_append v (of_array values)

let append_list v values =
  match values with
  | [] -> v
  | _ -> append_array v (Array.of_list values)

let append_seq v values =
  append_array v (Array.of_seq values)

let to_list v = Array.to_list (to_array v)

let of_seq values = append_seq empty values

let to_seq v =
  let rec next index () =
    if index = v.count then Seq.Nil else Seq.Cons (get v index, next (index + 1))
  in
  next 0
