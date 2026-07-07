let bits = 5
let width = 1 lsl bits

type 'a node =
  | Empty
  | Leaf of 'a array
  | Branch of {
      children : 'a node array;
      sizes : int array option;
      count : int;
      height : int;
    }

type 'a t = {
  count : int;
  root : 'a node;
  tail : 'a array;
  tailoff : int;
  head : 'a array;
}

let empty =
  {
    count = 0;
    root = Empty;
    tail = [||];
    tailoff = 0;
    head = [||];
  }

let length v = v.count

let is_empty v = v.count = 0

let invalid_index () = invalid_arg "index out of bounds"

let node_count = function
  | Empty -> 0
  | Leaf values -> Array.length values
  | Branch branch -> branch.count

let node_height = function
  | Empty -> -1
  | Leaf _ -> 0
  | Branch branch -> branch.height

let ceil_div a b = (a + b - 1) / b

let single_child_branch child =
  Branch
    {
      children = [| child |];
      sizes = None;
      count = node_count child;
      height = node_height child + 1;
    }

let rec promote_to_height height child =
  if node_height child = height then child
  else promote_to_height height (single_child_branch child)

let normalize_child_heights children =
  let length = Array.length children in
  if length = 0 then children
  else
    let max_height = ref (node_height (Array.unsafe_get children 0)) in
    let same_height = ref true in
    for i = 1 to length - 1 do
      let height = node_height (Array.unsafe_get children i) in
      if height <> !max_height then same_height := false;
      if height > !max_height then max_height := height
    done;
    if !same_height then children
    else
      let normalized = Array.copy children in
      for i = 0 to length - 1 do
        let child = Array.unsafe_get normalized i in
        if node_height child <> !max_height then
          Array.unsafe_set normalized i (promote_to_height !max_height child)
      done;
      normalized

let make_with_edges head root tail =
  let root_count = node_count root in
  {
    count = Array.length head + root_count + Array.length tail;
    root;
    tail;
    tailoff = Array.length head + root_count;
    head;
  }

let capacities =
  let rec loop capacity acc =
    let acc = capacity :: acc in
    if capacity = max_int then Array.of_list (List.rev acc)
    else if capacity > max_int / width then loop max_int acc
    else loop (capacity * width) acc
  in
  loop width []

let capacities_length = Array.length capacities
let capacity_height_1 = Array.unsafe_get capacities 1
let capacity_height_2 = Array.unsafe_get capacities 2

let capacity_for_height height =
  match height with
  | 0 -> width
  | 1 -> capacity_height_1
  | 2 -> capacity_height_2
  | _ when height < 0 -> 0
  | _ when height < capacities_length -> Array.unsafe_get capacities height
  | _ -> max_int

let radix_shift height = bits * height

let radix_child_index height index =
  let shift = radix_shift height in
  if shift >= Sys.int_size then 0 else (index lsr shift) land (width - 1)

let find_child sizes height index =
  let length = Array.length sizes in
  let start = min (length - 1) (radix_child_index height index) in
  let rec loop child_index =
    if index < Array.unsafe_get sizes child_index then child_index
    else loop (child_index + 1)
  in
  loop start

let radix_offset height child_index =
  let shift = radix_shift height in
  if shift >= Sys.int_size then 0 else child_index lsl shift

let child_range sizes height index =
  match sizes with
  | None ->
      let child_index = radix_child_index height index in
      (child_index, radix_offset height child_index)
  | Some sizes ->
      let child_index = find_child sizes height index in
      let previous_size =
        if child_index = 0 then 0 else Array.unsafe_get sizes (child_index - 1)
      in
      (child_index, previous_size)

let child_stop_offset sizes height count child_index =
  match sizes with
  | None -> min count (radix_offset height (child_index + 1))
  | Some sizes -> Array.unsafe_get sizes child_index

let build_sizes children =
  let length = Array.length children in
  let sizes = Array.make length 0 in
  let count = ref 0 in
  for i = 0 to length - 1 do
    count := !count + node_count (Array.unsafe_get children i);
    Array.unsafe_set sizes i !count
  done;
  sizes

let make_branch_node children =
  let length = Array.length children in
  assert (length > 0);
  let children = normalize_child_heights children in
  let count = ref 0 in
  let child_height = node_height (Array.unsafe_get children 0) in
  let height = child_height + 1 in
  let child_capacity = capacity_for_height child_height in
  let regular = ref true in
  for i = 0 to length - 1 do
    let child = Array.unsafe_get children i in
    let child_count = node_count child in
    assert (child_count > 0);
    count := !count + child_count;
    if i < length - 1 then regular := !regular && child_count = child_capacity;
  done;
  Branch
    {
      children;
      sizes = (if !regular then None else Some (build_sizes children));
      count = !count;
      height;
    }

let make_branch children =
  let length = Array.length children in
  assert (length > 0);
  if length = 1 then Array.unsafe_get children 0 else make_branch_node children

let rec last_leaf_node = function
  | Empty -> invalid_index ()
  | Leaf values -> values
  | Branch branch ->
      last_leaf_node
        (Array.unsafe_get branch.children (Array.length branch.children - 1))

let rec take_last_leaf_node = function
  | Empty -> invalid_index ()
  | Leaf values -> (values, None)
  | Branch branch ->
      let child_index = Array.length branch.children - 1 in
      let leaf, child =
        take_last_leaf_node (Array.unsafe_get branch.children child_index)
      in
      let children =
        match child with
        | None -> Array.sub branch.children 0 child_index
        | Some child ->
            let children = Array.copy branch.children in
            Array.unsafe_set children child_index child;
            children
      in
      let root =
        if Array.length children = 0 then None else Some (make_branch children)
      in
      (leaf, root)

let rec first_leaf_node = function
  | Empty -> invalid_index ()
  | Leaf values -> values
  | Branch branch -> first_leaf_node (Array.unsafe_get branch.children 0)

let rec remove_last_leaf_node = function
  | Empty -> None
  | Leaf _ -> None
  | Branch branch ->
      let child_index = Array.length branch.children - 1 in
      let children =
        match remove_last_leaf_node (Array.unsafe_get branch.children child_index) with
        | None -> Array.sub branch.children 0 child_index
        | Some child ->
            let children = Array.copy branch.children in
            Array.unsafe_set children child_index child;
            children
      in
      if Array.length children = 0 then None else Some (make_branch children)

let rec remove_first_leaf_node = function
  | Empty -> None
  | Leaf _ -> None
  | Branch branch ->
      let children =
        match remove_first_leaf_node (Array.unsafe_get branch.children 0) with
        | None -> Array.sub branch.children 1 (Array.length branch.children - 1)
        | Some child ->
            let children = Array.copy branch.children in
            Array.unsafe_set children 0 child;
            children
      in
      if Array.length children = 0 then None else Some (make_branch children)

let make_vector root =
  match root with
  | Empty -> empty
  | Leaf values -> make_with_edges [||] Empty values
  | Branch _ ->
      let tail = last_leaf_node root in
      let root = remove_last_leaf_node root |> Option.value ~default:Empty in
      let head, root =
        match root with
        | Empty -> ([||], Empty)
        | Leaf values when Array.length values < width -> (values, Empty)
        | Leaf _ -> ([||], root)
        | Branch _ ->
            let head = first_leaf_node root in
            if Array.length head < width then
              let root =
                remove_first_leaf_node root |> Option.value ~default:Empty
              in
              (head, root)
            else ([||], root)
      in
      make_with_edges head root tail

let full_rebalance_window length is_full =
  let left_keep = ref 0 in
  while !left_keep < length && is_full !left_keep do
    incr left_keep
  done;
  let right_keep = ref length in
  while !right_keep > !left_keep && is_full (!right_keep - 1) do
    decr right_keep
  done;
  (!left_keep, !right_keep)

let count_window_units unit_count left_keep right_keep =
  let units = ref 0 in
  for i = left_keep to right_keep - 1 do
    units := !units + unit_count i
  done;
  !units

let make_rebalance_result children left_keep right_keep window_groups =
  let length = Array.length children in
  let suffix_length = length - right_keep in
  let result_length = left_keep + window_groups + suffix_length in
  let result = Array.make result_length (Array.unsafe_get children 0) in
  Array.blit children 0 result 0 left_keep;
  Array.blit children right_keep result (left_keep + window_groups) suffix_length;
  result

let rebalance_branch_children children =
  let children = normalize_child_heights children in
  if Array.length children <= 1 then children
  else
    match Array.unsafe_get children 0 with
    | Leaf _ ->
        let length = Array.length children in
        let total_values = ref 0 in
        let can_rebalance = ref true in
        for i = 0 to length - 1 do
          match Array.unsafe_get children i with
          | Leaf values -> total_values := !total_values + Array.length values
          | Empty | Branch _ -> can_rebalance := false
        done;
        let opt = ceil_div !total_values width in
        if (not !can_rebalance) || length <= opt + 2 then children
        else
          let leaf_length index =
            match Array.unsafe_get children index with
            | Leaf values -> Array.length values
            | Empty | Branch _ -> assert false
          in
          let left_keep, right_keep =
            full_rebalance_window length (fun index ->
                leaf_length index = width)
          in
          let window_values =
            count_window_units leaf_length left_keep right_keep
          in
          let window_groups = ceil_div window_values width in
          let result =
            make_rebalance_result children left_keep right_keep window_groups
          in
          let source_index = ref left_keep in
          let source_offset = ref 0 in
          let next_value () =
            match Array.unsafe_get children !source_index with
            | Leaf values ->
                let value = Array.unsafe_get values !source_offset in
                incr source_offset;
                if !source_offset = Array.length values then (
                  incr source_index;
                  source_offset := 0);
                value
            | Empty | Branch _ -> assert false
          in
          let remaining = ref window_values in
          for group_index = 0 to window_groups - 1 do
            let group_length = min width !remaining in
            let first = next_value () in
            let values = Array.make group_length first in
            for value_index = 1 to group_length - 1 do
              Array.unsafe_set values value_index (next_value ())
            done;
            remaining := !remaining - group_length;
            Array.unsafe_set result (left_keep + group_index) (Leaf values)
          done;
          result
    | Branch first_branch ->
        let length = Array.length children in
        let height = first_branch.height in
        let total_child_slots = ref 0 in
        let can_rebalance = ref true in
        for i = 0 to length - 1 do
          match Array.unsafe_get children i with
          | Branch branch when branch.height = height ->
              total_child_slots := !total_child_slots + Array.length branch.children
          | Empty | Leaf _ | Branch _ -> can_rebalance := false
        done;
        let opt = ceil_div !total_child_slots width in
        if (not !can_rebalance) || length <= opt + 2 then children
        else
          let branch_child_slots index =
            match Array.unsafe_get children index with
            | Branch branch -> Array.length branch.children
            | Empty | Leaf _ -> assert false
          in
          let left_keep, right_keep =
            full_rebalance_window length (fun index ->
                branch_child_slots index = width)
          in
          let window_slots =
            count_window_units branch_child_slots left_keep right_keep
          in
          let window_groups = ceil_div window_slots width in
          let result =
            make_rebalance_result children left_keep right_keep window_groups
          in
          let source_index = ref left_keep in
          let source_offset = ref 0 in
          let next_child () =
            match Array.unsafe_get children !source_index with
            | Branch branch ->
                let child = Array.unsafe_get branch.children !source_offset in
                incr source_offset;
                if !source_offset = Array.length branch.children then (
                  incr source_index;
                  source_offset := 0);
                child
            | Empty | Leaf _ -> assert false
          in
          let remaining = ref window_slots in
          for group_index = 0 to window_groups - 1 do
            let group_length = min width !remaining in
            let first = next_child () in
            let group_children = Array.make group_length first in
            for child_index = 1 to group_length - 1 do
              Array.unsafe_set group_children child_index (next_child ())
            done;
            remaining := !remaining - group_length;
            Array.unsafe_set result (left_keep + group_index)
              (make_branch_node group_children)
          done;
          result
    | Empty -> children

let make_concat_branch children = make_branch (rebalance_branch_children children)

let node_full node =
  let capacity = capacity_for_height (node_height node) in
  capacity <> 0 && node_count node >= capacity

let node_full_at_height height node =
  let capacity = capacity_for_height height in
  capacity <> 0 && node_count node >= capacity

let rec new_path height leaf =
  if height = 0 then leaf else single_child_branch (new_path (height - 1) leaf)

let append_child children child =
  let length = Array.length children in
  let children' = Array.make (length + 1) child in
  Array.blit children 0 children' 0 length;
  children'

let prepend_child child children =
  let length = Array.length children in
  let children' = Array.make (length + 1) child in
  Array.blit children 0 children' 1 length;
  children'

let update_sizes sizes start delta =
  let sizes' = Array.copy sizes in
  for i = start to Array.length sizes - 1 do
    Array.unsafe_set sizes' i (Array.unsafe_get sizes i + delta)
  done;
  sizes'

let replace_branch_child node child_index child delta =
  match node with
  | Branch branch ->
      let children = Array.copy branch.children in
      assert (node_height child = branch.height - 1);
      Array.unsafe_set children child_index child;
      let sizes =
        match branch.sizes with
        | None ->
            if
              child_index = Array.length children - 1
              || node_full_at_height (branch.height - 1) child
            then None
            else Some (build_sizes children)
        | Some sizes -> Some (update_sizes sizes child_index delta)
      in
      Branch
        {
          children;
          sizes;
          count = branch.count + delta;
          height = branch.height;
        }
  | Empty | Leaf _ -> invalid_arg "expected branch"

let append_branch_child node child child_count =
  match node with
  | Branch branch ->
      let length = Array.length branch.children in
      let children = append_child branch.children child in
      let sizes =
        match branch.sizes with
        | None ->
            let previous_last = Array.unsafe_get branch.children (length - 1) in
            if node_full_at_height (branch.height - 1) previous_last then None
            else Some (build_sizes children)
        | Some sizes ->
            let sizes' = Array.make (length + 1) (branch.count + child_count) in
            Array.blit sizes 0 sizes' 0 length;
            Some sizes'
      in
      Branch
        {
          children;
          sizes;
          count = branch.count + child_count;
          height = branch.height;
        }
  | Empty | Leaf _ -> invalid_arg "expected branch"

let prepend_branch_child node child child_count =
  match node with
  | Branch branch ->
      let length = Array.length branch.children in
      let children = prepend_child child branch.children in
      let sizes =
        match branch.sizes with
        | None ->
            if node_full_at_height (branch.height - 1) child then None
            else Some (build_sizes children)
        | Some sizes ->
            let sizes' = Array.make (length + 1) 0 in
            Array.unsafe_set sizes' 0 child_count;
            for i = 0 to length - 1 do
              Array.unsafe_set sizes' (i + 1)
                (child_count + Array.unsafe_get sizes i)
            done;
            Some sizes'
      in
      Branch
        {
          children;
          sizes;
          count = branch.count + child_count;
          height = branch.height;
        }
  | Empty | Leaf _ -> invalid_arg "expected branch"

type 'a leaf_insert =
  {
    mutable leaf_inserted : bool;
    mutable leaf_node : 'a node;
  }

let set_leaf_inserted result node =
  result.leaf_inserted <- true;
  result.leaf_node <- node

let set_leaf_split result node =
  result.leaf_inserted <- false;
  result.leaf_node <- node

let rec insert_leaf result height node leaf leaf_count =
  if height = 0 then set_leaf_split result leaf
  else
    match node with
    | Branch branch ->
        let child_height = height - 1 in
        let branch_length = Array.length branch.children in
        let child_index = branch_length - 1 in
        let child = Array.unsafe_get branch.children child_index in
        if node_full_at_height child_height child then
          if branch_length < width then
            set_leaf_inserted result
              (append_branch_child node (new_path child_height leaf) leaf_count)
          else set_leaf_split result (new_path height leaf)
        else (
          insert_leaf result child_height child leaf leaf_count;
          if result.leaf_inserted then
            set_leaf_inserted result
              (replace_branch_child node child_index result.leaf_node leaf_count)
          else if branch_length < width then
            set_leaf_inserted result
              (append_branch_child node result.leaf_node leaf_count)
          else set_leaf_split result (new_path height leaf))
    | Empty | Leaf _ -> set_leaf_split result leaf

let append_full_leaf root leaf =
  match root with
  | Empty -> leaf
  | Leaf _ -> make_branch_node [| root; leaf |]
  | Branch _ -> (
      let height = node_height root in
      if node_full root then make_branch_node [| root; new_path height leaf |]
      else (
        let result = { leaf_inserted = false; leaf_node = Empty } in
        insert_leaf result height root leaf (node_count leaf);
        if result.leaf_inserted then result.leaf_node
        else make_branch_node [| root; result.leaf_node |]))

let rec insert_leaf_front result height node leaf leaf_count =
  if height = 0 then set_leaf_split result leaf
  else
    match node with
    | Branch branch ->
        let child_height = height - 1 in
        let branch_length = Array.length branch.children in
        let child = Array.unsafe_get branch.children 0 in
        if node_full_at_height child_height child then
          if branch_length < width then
            set_leaf_inserted result
              (prepend_branch_child node (new_path child_height leaf) leaf_count)
          else set_leaf_split result (new_path height leaf)
        else (
          insert_leaf_front result child_height child leaf leaf_count;
          if result.leaf_inserted then
            set_leaf_inserted result
              (replace_branch_child node 0 result.leaf_node leaf_count)
          else if branch_length < width then
            set_leaf_inserted result
              (prepend_branch_child node result.leaf_node leaf_count)
          else set_leaf_split result (new_path height leaf))
    | Empty | Leaf _ -> set_leaf_split result leaf

let prepend_full_leaf root leaf =
  match root with
  | Empty -> leaf
  | Leaf _ -> make_branch_node [| leaf; root |]
  | Branch _ -> (
      let height = node_height root in
      if node_full root then make_branch_node [| new_path height leaf; root |]
      else (
        let result = { leaf_inserted = false; leaf_node = Empty } in
        insert_leaf_front result height root leaf (node_count leaf);
        if result.leaf_inserted then result.leaf_node
        else make_branch_node [| result.leaf_node; root |]))

let append_arrays left right =
  let left_length = Array.length left in
  let right_length = Array.length right in
  if left_length = 0 then Array.copy right
  else if right_length = 0 then Array.copy left
  else
    let values = Array.make (left_length + right_length) (Array.unsafe_get left 0) in
    Array.blit left 0 values 0 left_length;
    Array.blit right 0 values left_length right_length;
    values

let prepend_value values value =
  let length = Array.length values in
  let values' = Array.make (length + 1) value in
  Array.blit values 0 values' 1 length;
  values'

let append_value values value =
  let length = Array.length values in
  let values' = Array.make (length + 1) value in
  Array.blit values 0 values' 0 length;
  values'

let combine_children left right =
  match (left, right) with
  | Branch left_branch, Branch right_branch
    when left_branch.height = right_branch.height
         && Array.length left_branch.children + Array.length right_branch.children
            <= width ->
      Some (Array.append left_branch.children right_branch.children)
  | Branch branch, node
    when branch.height = node_height node + 1
         && Array.length branch.children < width ->
      Some (append_child branch.children node)
  | node, Branch branch
    when node_height node + 1 = branch.height
         && Array.length branch.children < width ->
      Some (prepend_child node branch.children)
  | _ -> None

let array_without_last values =
  Array.sub values 0 (Array.length values - 1)

let array_replace_last values value =
  let values' = Array.copy values in
  Array.unsafe_set values' (Array.length values' - 1) value;
  values'

let array_replace_first values value =
  let values' = Array.copy values in
  Array.unsafe_set values' 0 value;
  values'

let rec concat_nodes left right =
  match (left, right) with
  | Empty, node | node, Empty -> node
  | Leaf left_values, Leaf right_values
    when Array.length left_values + Array.length right_values <= width ->
      Leaf (append_arrays left_values right_values)
  | _ when node_height left > node_height right + 1 -> (
      match left with
      | Branch branch ->
          let rightmost =
            Array.unsafe_get branch.children (Array.length branch.children - 1)
          in
          let merged = concat_nodes rightmost right in
          make_concat_branch (array_replace_last branch.children merged)
      | Empty | Leaf _ -> make_concat_branch [| left; right |])
  | _ when node_height right > node_height left + 1 -> (
      match right with
      | Branch branch ->
          let leftmost = Array.unsafe_get branch.children 0 in
          let merged = concat_nodes left leftmost in
          make_concat_branch (array_replace_first branch.children merged)
      | Empty | Leaf _ -> make_concat_branch [| left; right |])
  | _ -> (
      match combine_children left right with
      | Some children -> make_concat_branch children
      | None -> make_concat_branch [| left; right |])

let rec get_node node index =
  match node with
  | Empty -> invalid_index ()
  | Leaf values -> Array.unsafe_get values index
  | Branch branch ->
      let child_index, previous_size =
        child_range branch.sizes branch.height index
      in
      get_node
        (Array.unsafe_get branch.children child_index)
        (index - previous_size)

let get v index =
  if index < 0 || index >= v.count then invalid_index ();
  let head_length = Array.length v.head in
  if index < head_length then Array.unsafe_get v.head index
  else if index >= v.tailoff then Array.unsafe_get v.tail (index - v.tailoff)
  else get_node v.root (index - head_length)

let rec set_node node index value =
  match node with
  | Empty -> invalid_index ()
  | Leaf values ->
      let values' = Array.copy values in
      Array.unsafe_set values' index value;
      Leaf values'
  | Branch branch ->
      let child_index, previous_size =
        child_range branch.sizes branch.height index
      in
      let children = Array.copy branch.children in
      Array.unsafe_set children child_index
        (set_node
           (Array.unsafe_get branch.children child_index)
           (index - previous_size) value);
      Branch { branch with children }

let push_back_impl v value =
  let tail_length = Array.length v.tail in
  if tail_length < width then
    {
      v with
      count = v.count + 1;
      tail = append_value v.tail value;
    }
  else
    let root = append_full_leaf v.root (Leaf v.tail) in
    {
      count = v.count + 1;
      root;
      tail = [| value |];
      tailoff = Array.length v.head + node_count root;
      head = v.head;
    }

let set v index value =
  if index < 0 || index >= v.count then invalid_index ();
  let head_length = Array.length v.head in
  if index < head_length then (
    let head = Array.copy v.head in
    Array.unsafe_set head index value;
    { v with head })
  else if index >= v.tailoff then (
    let tail = Array.copy v.tail in
    Array.unsafe_set tail (index - v.tailoff) value;
    { v with tail })
  else make_with_edges v.head (set_node v.root (index - head_length) value) v.tail

let peek_back_impl v =
  if v.count = 0 then invalid_index ();
  let tail_length = Array.length v.tail in
  if tail_length > 0 then Array.unsafe_get v.tail (tail_length - 1)
  else if v.root <> Empty then get_node v.root (node_count v.root - 1)
  else
    let head_length = Array.length v.head in
    Array.unsafe_get v.head (head_length - 1)

let pull_tail_from_root root =
  let tail, root = take_last_leaf_node root in
  (Option.value root ~default:Empty, tail)

let refill_tail_if_empty root tail =
  if Array.length tail > 0 || root = Empty then (root, tail)
  else pull_tail_from_root root

let fold_array_range f acc values start stop =
  let acc = ref acc in
  for i = start to stop - 1 do
    acc := f !acc (Array.unsafe_get values i)
  done;
  !acc

let fold_array_right_range f values start stop acc =
  let acc = ref acc in
  for i = stop - 1 downto start do
    acc := f (Array.unsafe_get values i) !acc
  done;
  !acc

let rec fold_left_node f acc node =
  match node with
  | Empty -> acc
  | Leaf values -> fold_array_range f acc values 0 (Array.length values)
  | Branch branch ->
      let acc = ref acc in
      for i = 0 to Array.length branch.children - 1 do
        acc := fold_left_node f !acc (Array.unsafe_get branch.children i)
      done;
      !acc

let fold_left f acc v =
  let acc = fold_array_range f acc v.head 0 (Array.length v.head) in
  let acc = fold_left_node f acc v.root in
  fold_array_range f acc v.tail 0 (Array.length v.tail)

let rec fold_right_node f node acc =
  match node with
  | Empty -> acc
  | Leaf values -> fold_array_right_range f values 0 (Array.length values) acc
  | Branch branch ->
      let acc = ref acc in
      for i = Array.length branch.children - 1 downto 0 do
        acc := fold_right_node f (Array.unsafe_get branch.children i) !acc
      done;
      !acc

let fold_right f v acc =
  let acc = fold_array_right_range f v.tail 0 (Array.length v.tail) acc in
  let acc = fold_right_node f v.root acc in
  fold_array_right_range f v.head 0 (Array.length v.head) acc

let leaf_if_nonempty values =
  if Array.length values = 0 then Empty else Leaf values

let middle_root left right =
  concat_nodes
    (concat_nodes left.root (leaf_if_nonempty left.tail))
    (concat_nodes (leaf_if_nonempty right.head) right.root)

let concat left right =
  if left.count = 0 then right
  else if right.count = 0 then left
  else if right.count <= width then
    fold_left (fun acc value -> push_back_impl acc value) left right
  else make_with_edges left.head (middle_root left right) right.tail

let push_back = push_back_impl

let push_front v value =
  let head_length = Array.length v.head in
  if head_length < width then
    {
      v with
      count = v.count + 1;
      head = prepend_value v.head value;
      tailoff = v.tailoff + 1;
    }
  else
    let root = prepend_full_leaf v.root (Leaf v.head) in
    {
      count = v.count + 1;
      root;
      tail = v.tail;
      tailoff = 1 + node_count root;
      head = [| value |];
    }

let pop_back v =
  if v.count = 0 then invalid_index ();
  let tail_length = Array.length v.tail in
  if tail_length > 0 then
    let value = Array.unsafe_get v.tail (tail_length - 1) in
    if tail_length > 1 then
      ( value,
        {
          v with
          count = v.count - 1;
          tail = Array.sub v.tail 0 (tail_length - 1);
        } )
    else if v.root = Empty then
      (value, { v with count = v.count - 1; tail = [||] })
    else
      let root, tail = pull_tail_from_root v.root in
      ( value,
        {
          count = v.count - 1;
          root;
          tail;
          tailoff = Array.length v.head + node_count root;
          head = v.head;
        } )
  else if v.root = Empty then
    let head_length = Array.length v.head in
    let value = Array.unsafe_get v.head (head_length - 1) in
    if head_length = 1 then (value, empty)
    else
      ( value,
        {
          v with
          count = v.count - 1;
          head = Array.sub v.head 0 (head_length - 1);
          tailoff = v.tailoff - 1;
        } )
  else
    let leaf, root = take_last_leaf_node v.root in
    let leaf_length = Array.length leaf in
    let value = Array.unsafe_get leaf (leaf_length - 1) in
    let root = Option.value root ~default:Empty in
    let tail = Array.sub leaf 0 (leaf_length - 1) in
    let root, tail = refill_tail_if_empty root tail in
    ( value,
      {
        count = v.count - 1;
        root;
        tail;
        tailoff = Array.length v.head + node_count root;
        head = v.head;
      } )

let peek_back = peek_back_impl

let peek_front v =
  if v.count = 0 then invalid_index ();
  if Array.length v.head > 0 then Array.unsafe_get v.head 0
  else if v.root <> Empty then get_node v.root 0
  else Array.unsafe_get v.tail 0

let append = concat

let prepend left right =
  concat left right

let to_array v =
  if v.count = 0 then [||]
  else
    let values = Array.make v.count (get v 0) in
    let position = ref 0 in
    fold_left
      (fun () value ->
        Array.unsafe_set values !position value;
        incr position)
      () v;
    values

let rec build_level nodes =
  let length = Array.length nodes in
  if length = 1 then Array.unsafe_get nodes 0
  else
    let parent_count = (length + width - 1) / width in
    let parents =
      Array.init parent_count (fun parent_index ->
          let start = parent_index * width in
          let stop = min length (start + width) in
          make_branch_node (Array.sub nodes start (stop - start)))
    in
    build_level parents

let of_array values =
  let count = Array.length values in
  if count = 0 then empty
  else
    let tail_length =
      let remainder = count mod width in
      if count <= width then count else if remainder = 0 then width else remainder
    in
    let tail_start = count - tail_length in
    let tail = Array.sub values tail_start tail_length in
    if tail_start = 0 then make_with_edges [||] Empty tail
    else
      let leaf_count = tail_start / width in
      let leaves =
        Array.init leaf_count (fun leaf_index ->
            let start = leaf_index * width in
            Leaf (Array.sub values start width))
      in
      make_with_edges [||] (build_level leaves) tail

let leaf_slice values start stop =
  if start = 0 && stop = Array.length values then Leaf values
  else Leaf (Array.sub values start (stop - start))

let rec slice_node node start stop =
  if start = 0 && stop = node_count node then node
  else
    match node with
    | Empty -> Empty
    | Leaf values -> leaf_slice values start stop
    | Branch branch ->
        let first_child, first_child_start =
          child_range branch.sizes branch.height start
        in
        let last_child, _last_child_start =
          child_range branch.sizes branch.height (stop - 1)
        in
        if first_child = last_child then
          slice_node
            (Array.unsafe_get branch.children first_child)
            (start - first_child_start) (stop - first_child_start)
        else
          let children = ref [] in
          for child_index = first_child to last_child do
            let child = Array.unsafe_get branch.children child_index in
            let child_start =
              if child_index = first_child then first_child_start
              else
                match branch.sizes with
                | None -> radix_offset branch.height child_index
                | Some sizes -> Array.unsafe_get sizes (child_index - 1)
            in
            let child_stop =
              child_stop_offset branch.sizes branch.height branch.count child_index
            in
            let child_slice_start =
              if child_index = first_child then start - child_start else 0
            in
            let child_slice_stop =
              if child_index = last_child then stop - child_start
              else child_stop - child_start
            in
            let child =
              if child_slice_start = 0 && child_slice_stop = node_count child then
                child
              else slice_node child child_slice_start child_slice_stop
            in
            children := child :: !children
          done;
          make_branch (Array.of_list (List.rev !children))

let concat_array_slice node values start stop =
  if start = stop then node else concat_nodes node (leaf_slice values start stop)

let concat_node_slice node slice =
  match slice with Empty -> node | Leaf _ | Branch _ -> concat_nodes node slice

let rec compact_root = function
  | Branch branch when Array.length branch.children = 1 ->
      compact_root (Array.unsafe_get branch.children 0)
  | node -> node

let subvec v start stop =
  if start < 0 || stop < start || stop > v.count then invalid_index ();
  let count = stop - start in
  if count = 0 then empty
  else
    let head_length = Array.length v.head in
    let root_start = head_length in
    let root_stop = v.tailoff in
    let node = ref Empty in
    if start < head_length then
      (node :=
         concat_array_slice !node v.head start (min stop head_length));
    if start < root_stop && stop > root_start then (
      let slice_start = max start root_start - root_start in
      let slice_stop = min stop root_stop - root_start in
      node := concat_node_slice !node (slice_node v.root slice_start slice_stop));
    if stop > v.tailoff then
      (node :=
         concat_array_slice !node v.tail (max start v.tailoff - v.tailoff)
           (stop - v.tailoff));
    make_vector (compact_root !node)

let pop_front v =
  if v.count = 0 then invalid_index ();
  let head_length = Array.length v.head in
  if head_length > 0 then
    let value = Array.unsafe_get v.head 0 in
    let head = Array.sub v.head 1 (head_length - 1) in
    (value, { v with count = v.count - 1; head; tailoff = v.tailoff - 1 })
  else if v.root <> Empty then
    let leaf = first_leaf_node v.root in
    let value = Array.unsafe_get leaf 0 in
    let head = Array.sub leaf 1 (Array.length leaf - 1) in
    let root = remove_first_leaf_node v.root |> Option.value ~default:Empty in
    ( value,
      {
        count = v.count - 1;
        root;
        tail = v.tail;
        tailoff = Array.length head + node_count root;
        head;
      } )
  else
    let value = Array.unsafe_get v.tail 0 in
    let tail = Array.sub v.tail 1 (Array.length v.tail - 1) in
    (value, { v with count = v.count - 1; tail; tailoff = 0 })

let rec map_node f = function
  | Empty -> Empty
  | Leaf values -> Leaf (Array.map f values)
  | Branch branch ->
      let children = Array.map (map_node f) branch.children in
      Branch { branch with children }

let map f v =
  if v.count = 0 then empty
  else
    let head = Array.map f v.head in
    let root = map_node f v.root in
    let tail = Array.map f v.tail in
    {
      count = v.count;
      root;
      tail;
      tailoff = v.tailoff;
      head;
    }

let append_array v values =
  if Array.length values = 0 then v else concat v (of_array values)

let append_list v values =
  match values with
  | [] -> v
  | _ -> append_array v (Array.of_list values)

let prepend_list v values =
  match values with
  | [] -> v
  | _ -> prepend (of_array (Array.of_list values)) v

let prepend_arrat v values =
  if Array.length values = 0 then v else prepend (of_array values) v

let of_list values = of_array (Array.of_list values)

let to_list v = Array.to_list (to_array v)

(*
  Internal invariants checked by [invariants]:

  - The empty vector has one canonical representation.
  - Vector [count], [tailoff], [head], and [tail] match the root metadata.
  - [Leaf] nodes are non-empty, contain at most [width] elements, and report
    height zero and one leaf to their parent.
  - [Branch] nodes contain between one and [width] non-empty children.
  - All direct children of a [Branch] have height [branch.height - 1].
  - Branch [sizes] are absent for radix-regular nodes. Relaxed branch [sizes]
    are cumulative child ranges, strictly increasing, and the last range equals
    the branch element count.
  - Branch [count] and [height] match their children.
  - A root [Branch] has more than one child; internal singleton branches are
    still allowed to preserve height.
  - Relaxed search steps and root height stay within smoke-test bounds.
*)
let invariant_errorf path fmt =
  Printf.ksprintf
    (fun message -> failwith ("rrbvec invariant at " ^ path ^ ": " ^ message))
    fmt

let require path condition fmt =
  Printf.ksprintf
    (fun message -> if not condition then invariant_errorf path "%s" message)
    fmt

let child_path path index = path ^ ".children[" ^ string_of_int index ^ "]"

let arity = function
  | Empty -> 0
  | Leaf values -> Array.length values
  | Branch branch -> Array.length branch.children

let rec rightmost_leaf_length = function
  | Empty -> 0
  | Leaf values -> Array.length values
  | Branch branch ->
      rightmost_leaf_length
        (Array.unsafe_get branch.children (Array.length branch.children - 1))

let rec is_full_node node =
  match node with
  | Empty -> false
  | Leaf values -> Array.length values = width
  | Branch branch ->
      branch.count = capacity_for_height branch.height
      && Array.for_all is_full_node branch.children

let rec is_leftwise_dense node =
  match node with
  | Empty | Leaf _ -> true
  | Branch branch ->
      let length = Array.length branch.children in
      let dense = ref true in
      for i = 0 to length - 2 do
        dense := !dense && is_full_node (Array.unsafe_get branch.children i)
      done;
      !dense
      && is_leftwise_dense (Array.unsafe_get branch.children (length - 1))

let rec check_node root path node =
  match node with
  | Empty ->
      require path root "empty node is only allowed as the root";
      (0, -1, 0)
  | Leaf values ->
      let length = Array.length values in
      require path (length > 0) "leaf length must be positive";
      require path (length <= width) "leaf length %d exceeds width %d" length width;
      (length, 0, 1)
  | Branch branch ->
      let length = Array.length branch.children in
      require path (length >= 1) "branch must have at least one child";
      require path (length <= width) "branch child count %d exceeds width %d" length width;
      (match branch.sizes with
      | None -> ()
      | Some sizes ->
          require path
            (Array.length sizes = length)
            "sizes length %d must equal children length %d"
            (Array.length sizes) length);
      require path (branch.height >= 1) "branch height %d must be >= 1"
        branch.height;
      require path (branch.count > 0) "branch count %d must be positive"
        branch.count;
      let expected_child_height = branch.height - 1 in
      let count = ref 0 in
      let leaves = ref 0 in
      for i = 0 to length - 1 do
        let child_count, child_height, child_leaves =
          check_node false (child_path path i)
            (Array.unsafe_get branch.children i)
        in
        require (child_path path i)
          (child_height = expected_child_height)
          "child height must equal branch height - 1: expected %d, got %d"
          expected_child_height child_height;
        require (child_path path i) (child_count > 0)
          "child count %d must be positive" child_count;
        count := !count + child_count;
        leaves := !leaves + child_leaves;
        (match branch.sizes with
        | None ->
            if i < length - 1 then
              require (child_path path i)
                (child_count = capacity_for_height child_height)
                "regular branch child must be full: expected %d, got %d"
                (capacity_for_height child_height) child_count
        | Some sizes ->
            let size = Array.unsafe_get sizes i in
            require path (size = !count)
              "sizes.(%d) must equal prefix count %d, got %d" i !count size;
            if i > 0 then
              require path
                (Array.unsafe_get sizes (i - 1) < size)
                "sizes must be strictly increasing at index %d" i)
      done;
      require path (branch.count = !count)
        "branch count must equal child count sum: expected %d, got %d" !count
        branch.count;
      (match branch.sizes with
      | None -> ()
      | Some sizes ->
          require path
            (Array.unsafe_get sizes (length - 1) = branch.count)
            "last size must equal branch count: expected %d, got %d" branch.count
            (Array.unsafe_get sizes (length - 1)));
      require path
        (branch.count <= capacity_for_height branch.height)
        "branch count %d exceeds capacity %d for height %d" branch.count
        (capacity_for_height branch.height) branch.height;
      (branch.count, branch.height, !leaves)

let check_tail v root_count =
  let head_length = Array.length v.head in
  let tail_length = Array.length v.tail in
  require "vector" (head_length <= width) "head length %d exceeds width %d"
    head_length width;
  require "vector" (tail_length >= 0) "tail length must be non-negative";
  require "vector" (tail_length <= width) "tail length %d exceeds width %d"
    tail_length width;
  require "vector" (v.count >= 0) "vector count %d must be non-negative" v.count;
  require "vector" (v.tailoff >= 0) "tailoff %d must be non-negative" v.tailoff;
  require "vector" (v.tailoff <= v.count)
    "tailoff %d must be <= vector count %d" v.tailoff v.count;
  require "vector"
    (v.tailoff = head_length + root_count)
    "tailoff must equal head length + root count: expected %d, got %d"
    (head_length + root_count) v.tailoff;
  require "vector"
    (tail_length = v.count - v.tailoff)
    "tail length must equal count - tailoff: expected %d, got %d"
    (v.count - v.tailoff) tail_length;
  match v.root with
  | Empty ->
      require "vector"
        (v.tailoff = head_length)
        "empty root tailoff must equal head length: expected %d, got %d"
        head_length v.tailoff;
      require "vector"
        (v.count = head_length + tail_length)
        "empty root count must equal head length + tail length: expected %d, got %d"
        (head_length + tail_length) v.count
  | Leaf _ | Branch _ -> ()

let rec check_search_step_relaxed path node =
  match node with
  | Empty | Leaf _ -> ()
  | Branch branch ->
      let total_child_slots =
        Array.fold_left
          (fun acc child -> acc + arity child)
          0 branch.children
      in
      let opt = ceil_div total_child_slots width in
      require path
        (Array.length branch.children <= opt + 2)
        "relaxed search step too wide: children=%d, optimal=%d, emax=%d"
        (Array.length branch.children) opt 2;
      Array.iteri
        (fun index child -> check_search_step_relaxed (child_path path index) child)
        branch.children

let max_height_for_count ~base n =
  if n <= 0 then -1
  else
    let rec loop h cap =
      if n <= cap then h
      else
        let cap' = if cap > max_int / base then max_int else cap * base in
        loop (h + 1) cap'
    in
    loop 0 base

let check_height_bound v root_height =
  let emax = 2 in
  let base = width - emax - 1 in
  let bound = max_height_for_count ~base (max 1 v.tailoff) + 1 in
  require "vector"
    (root_height <= bound)
    "height bound exceeded: root height %d must be <= %d" root_height bound

let check_vector ?(strict = false) v =
  let root_count, root_height, _root_leaves = check_node true "root" v.root in
  (match v.root with
  | Empty ->
      require "vector" (root_count = 0) "empty root must have zero count";
      if v.count = 0 then (
        require "vector" (Array.length v.head = 0)
          "empty vector head must be empty";
        require "vector" (Array.length v.tail = 0)
          "empty vector tail must be empty";
        require "vector" (v.tailoff = 0) "empty vector tailoff must be zero")
  | Leaf _ -> require "vector" (root_count > 0) "leaf root must be non-empty"
  | Branch branch ->
      require "root"
        (Array.length branch.children > 1)
        "root branch must have more than one child";
      require "vector" (root_count > 0) "branch root must be non-empty");
  require "vector"
    (v.count > 0 || v.root = Empty)
    "zero-count vector root must be Empty";
  require "vector"
    (v.count = 0
    || v.root <> Empty
    || Array.length v.head > 0
    || Array.length v.tail > 0)
    "non-empty vector must contain a root, head, or tail segment";
  check_tail v root_count;
  check_search_step_relaxed "root" v.root;
  check_height_bound v root_height;
  if strict && is_leftwise_dense v.root && v.root <> Empty then
    require "root"
      (rightmost_leaf_length v.root = width)
      "rightmost leaf length must be width for a non-empty leftwise-dense root"

let check_strict_invariants v = check_vector ~strict:true v

let invariants v = check_vector v
