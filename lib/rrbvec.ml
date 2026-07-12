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

type 'a concat_forest = {
  forest_height : int;
  forest_nodes : 'a node array;
}

type 'a concat_level = {
  left_init : 'a node array;
  right_tail : 'a node array;
  child_height : int;
}

type 'a vector = {
  count : int;
  root : 'a node;
  tail : 'a array;
  tailoff : int;
  head : 'a array;
}

type 'a t =
  | Empty_vector
  | Vector of 'a vector

let empty = Empty_vector

let vector_or_empty v = if v.count = 0 then Empty_vector else Vector v

let length = function
  | Empty_vector -> 0
  | Vector v -> v.count

let is_empty = function
  | Empty_vector -> true
  | Vector _ -> false

let invalid_index () = invalid_arg "index out of bounds"

let ensure_count_growth count increment =
  if increment >= max_int || count >= max_int - increment then
    invalid_arg "Rrbvec: maximum length exceeded"

let node_count = function
  | Empty -> 0
  | Leaf values -> Array.length values
  | Branch branch -> branch.count

let node_height = function
  | Empty -> -1
  | Leaf _ -> 0
  | Branch branch -> branch.height

let make_concat_forest forest_height forest_nodes =
  { forest_height; forest_nodes }

let singleton_concat_forest node =
  make_concat_forest (node_height node) [| node |]

let make_concat_level ~left_init ~right_tail ~child_height =
  { left_init; right_tail; child_height }

let array_init_without_last values =
  let length = Array.length values in
  Array.sub values 0 (length - 1)

let array_tail_without_first values =
  let length = Array.length values in
  Array.sub values 1 (length - 1)

let ceil_div a b = (a + b - 1) / b

let make_with_edges head root tail =
  let root_count = node_count root in
  let count = Array.length head + root_count + Array.length tail in
  if count = 0 then Empty_vector
  else
    Vector
      {
        count;
        root;
        tail;
        tailoff = Array.length head + root_count;
        head;
      }

let singleton value = make_with_edges [||] Empty [| value |]

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

let make_strict_branch_node children =
  let length = Array.length children in
  let count = ref 0 in
  let child_height = node_height (Array.unsafe_get children 0) in
  let height = child_height + 1 in
  let child_capacity = capacity_for_height child_height in
  let regular = ref true in
  for i = 0 to length - 1 do
    let child = Array.unsafe_get children i in
    let child_count = node_count child in
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
  if length = 1 then Array.unsafe_get children 0
  else make_strict_branch_node children

let rebalance_concat_leaves left right =
  match (left, right) with
  | Leaf left_values, Leaf right_values ->
      let left_length = Array.length left_values in
      let right_length = Array.length right_values in
      if left_length = width then make_concat_forest 0 [| left; right |]
      else
        let total_length = left_length + right_length in
        if total_length <= width then (
          let values = Array.make total_length (Array.unsafe_get left_values 0) in
          Array.blit left_values 0 values 0 left_length;
          Array.blit right_values 0 values left_length right_length;
          singleton_concat_forest (Leaf values))
        else
          let left_result =
            Array.make width (Array.unsafe_get left_values 0)
          in
          let right_result_length = total_length - width in
          let right_result =
            Array.make right_result_length (Array.unsafe_get right_values 0)
          in
          Array.blit left_values 0 left_result 0 left_length;
          let right_values_in_left = width - left_length in
          Array.blit right_values 0 left_result left_length right_values_in_left;
          Array.blit right_values right_values_in_left right_result 0
            right_result_length;
          make_concat_forest 0 [| Leaf left_result; Leaf right_result |]
  | (Empty | Branch _), _ | _, (Empty | Branch _) ->
      invalid_arg "concat leaf rebalance requires two leaves"

let concat_node_arity = function
  | Empty -> invalid_arg "empty concat candidate"
  | Leaf values -> Array.length values
  | Branch branch -> Array.length branch.children

let concat_target_sizes candidates =
  let candidate_count = Array.length candidates in
  let sizes = Array.make candidate_count 0 in
  let total_slots = ref 0 in
  for index = 0 to candidate_count - 1 do
    let size = concat_node_arity (Array.unsafe_get candidates index) in
    Array.unsafe_set sizes index size;
    total_slots := !total_slots + size
  done;
  (* Scala Quick deliberately counts one effective slot beyond every complete
     block, including exact multiples of [width]. *)
  let effective = (!total_slots / width) + 1 in
  let allowed = effective + 2 in
  let target_count = ref candidate_count in
  while !target_count > allowed do
    let first_movable = ref 0 in
    while
      !first_movable < !target_count
      && Array.unsafe_get sizes !first_movable > width - 1
    do
      incr first_movable
    done;
    let index = ref !first_movable in
    let remainder = ref (Array.unsafe_get sizes !index) in
    while !remainder > 0 do
      let next_size = Array.unsafe_get sizes (!index + 1) in
      let moved_size = min (!remainder + next_size) width in
      Array.unsafe_set sizes !index moved_size;
      remainder := !remainder + next_size - moved_size;
      incr index
    done;
    while !index < !target_count - 1 do
      Array.unsafe_set sizes !index (Array.unsafe_get sizes (!index + 1));
      incr index
    done;
    decr target_count
  done;
  Array.sub sizes 0 !target_count

type 'a concat_source = {
  source_nodes : 'a node array;
  mutable source_index : int;
  mutable source_offset : int;
}

let advance_concat_source source source_arity =
  source.source_offset <- source.source_offset + 1;
  if source.source_offset = source_arity then (
    source.source_index <- source.source_index + 1;
    source.source_offset <- 0)

let next_concat_leaf_value source =
  match Array.unsafe_get source.source_nodes source.source_index with
  | Leaf values ->
      let value = Array.unsafe_get values source.source_offset in
      advance_concat_source source (Array.length values);
      value
  | Empty | Branch _ -> invalid_arg "mixed concat candidate heights"

let next_concat_branch_child source =
  match Array.unsafe_get source.source_nodes source.source_index with
  | Branch branch ->
      let child = Array.unsafe_get branch.children source.source_offset in
      advance_concat_source source (Array.length branch.children);
      child
  | Empty | Leaf _ -> invalid_arg "mixed concat candidate heights"

let redistribute_concat_candidates candidates targets =
  let candidate_count = Array.length candidates in
  let candidate_height = node_height (Array.unsafe_get candidates 0) in
  let source =
    { source_nodes = candidates; source_index = 0; source_offset = 0 }
  in
  Array.map
    (fun target_size ->
      if
        source.source_offset = 0
        && source.source_index < candidate_count
        && concat_node_arity (Array.unsafe_get candidates source.source_index)
           = target_size
      then
        let candidate = Array.unsafe_get candidates source.source_index in
        source.source_index <- source.source_index + 1;
        candidate
      else if candidate_height = 0 then
        Leaf (Array.init target_size (fun _ -> next_concat_leaf_value source))
      else
        let children =
          Array.init target_size (fun _ -> next_concat_branch_child source)
        in
        make_strict_branch_node children)
    targets

let concat_candidate_arrays left center right =
  let left_length = Array.length left in
  let center_length = Array.length center in
  let right_length = Array.length right in
  let candidates =
    Array.make (left_length + center_length + right_length)
      (Array.unsafe_get center 0)
  in
  Array.blit left 0 candidates 0 left_length;
  Array.blit center 0 candidates left_length center_length;
  Array.blit right 0 candidates (left_length + center_length) right_length;
  candidates

let pack_concat_parents child_height children =
  let child_count = Array.length children in
  let parent_count = ceil_div child_count width in
  let parents =
    Array.init parent_count (fun parent_index ->
        let start = parent_index * width in
        let group_length = min width (child_count - start) in
        let group = Array.sub children start group_length in
        make_strict_branch_node group)
  in
  make_concat_forest (child_height + 1) parents

let rebalance_concat_candidates node_height candidates =
  let targets = concat_target_sizes candidates in
  let redistributed = redistribute_concat_candidates candidates targets in
  if Array.length redistributed <= width then
    make_concat_forest node_height redistributed
  else pack_concat_parents node_height redistributed

let rebalance_and_pack_concat_candidates child_height candidates =
  let targets = concat_target_sizes candidates in
  let redistributed = redistribute_concat_candidates candidates targets in
  pack_concat_parents child_height redistributed

let propagate_concat_level level center =
  if center.forest_height <> level.child_height then
    invalid_arg "concat forest height changed before parent propagation";
  let candidates =
    concat_candidate_arrays level.left_init center.forest_nodes level.right_tail
  in
  rebalance_and_pack_concat_candidates level.child_height candidates

let rec concat_forests left right =
  let left_height = left.forest_height in
  let right_height = right.forest_height in
  if left_height = right_height then
    let left_count = Array.length left.forest_nodes in
    let right_count = Array.length right.forest_nodes in
    let left_boundary = Array.unsafe_get left.forest_nodes (left_count - 1) in
    let right_boundary = Array.unsafe_get right.forest_nodes 0 in
    let center =
      if left_height = 0 then
        rebalance_concat_leaves left_boundary right_boundary
      else
        match (left_boundary, right_boundary) with
        | Branch left_branch, Branch right_branch ->
            let level =
              make_concat_level
                ~left_init:(array_init_without_last left_branch.children)
                ~right_tail:(array_tail_without_first right_branch.children)
                ~child_height:(left_height - 1)
            in
            let lower_left =
              singleton_concat_forest
                (Array.unsafe_get left_branch.children
                   (Array.length left_branch.children - 1))
            in
            let lower_right =
              singleton_concat_forest
                (Array.unsafe_get right_branch.children 0)
            in
            propagate_concat_level level
              (concat_forests lower_left lower_right)
        | (Empty | Leaf _), _ | _, (Empty | Leaf _) ->
            invalid_arg "concat forest height does not match node shape"
    in
    let candidates =
      concat_candidate_arrays
        (Array.sub left.forest_nodes 0 (left_count - 1))
        center.forest_nodes
        (Array.sub right.forest_nodes 1 (right_count - 1))
    in
    rebalance_concat_candidates center.forest_height candidates
  else if left_height > right_height then
    let left_count = Array.length left.forest_nodes in
    let left_boundary = Array.unsafe_get left.forest_nodes (left_count - 1) in
    match left_boundary with
    | Branch left_branch ->
        let child_height = left_height - 1 in
        let level =
          make_concat_level
            ~left_init:(array_init_without_last left_branch.children)
            ~right_tail:[||] ~child_height
        in
        let lower_left =
          singleton_concat_forest
            (Array.unsafe_get left_branch.children
               (Array.length left_branch.children - 1))
        in
        let center = concat_forests lower_left right in
        let unwound = propagate_concat_level level center in
        let candidates =
          concat_candidate_arrays
            (Array.sub left.forest_nodes 0 (left_count - 1))
            unwound.forest_nodes [||]
        in
        rebalance_concat_candidates unwound.forest_height candidates
    | Empty | Leaf _ -> invalid_arg "taller concat forest must contain branches"
  else
    let right_count = Array.length right.forest_nodes in
    let right_boundary = Array.unsafe_get right.forest_nodes 0 in
    match right_boundary with
    | Branch right_branch ->
        let child_height = right_height - 1 in
        let level =
          make_concat_level ~left_init:[||]
            ~right_tail:(array_tail_without_first right_branch.children)
            ~child_height
        in
        let lower_right =
          singleton_concat_forest
            (Array.unsafe_get right_branch.children 0)
        in
        let center = concat_forests left lower_right in
        let unwound = propagate_concat_level level center in
        let candidates =
          concat_candidate_arrays [||] unwound.forest_nodes
            (Array.sub right.forest_nodes 1 (right_count - 1))
        in
        rebalance_concat_candidates unwound.forest_height candidates
    | Empty | Leaf _ -> invalid_arg "taller concat forest must contain branches"

let concat_middle_forest left right =
  let fragments = ref [] in
  let add_fragment node =
    if node <> Empty then fragments := node :: !fragments
  in
  add_fragment left.root;
  if Array.length left.tail > 0 then add_fragment (Leaf left.tail);
  if Array.length right.head > 0 then add_fragment (Leaf right.head);
  add_fragment right.root;
  match List.rev !fragments with
  | [] -> None
  | first :: rest ->
      Some
        (List.fold_left
           (fun forest node ->
             concat_forests forest (singleton_concat_forest node))
           (singleton_concat_forest first) rest)

let rec collapse_root = function
  | Branch branch when Array.length branch.children = 1 ->
      collapse_root (Array.unsafe_get branch.children 0)
  | node -> node

let concat_root = function
  | None -> Empty
  | Some forest ->
      let length = Array.length forest.forest_nodes in
      if length = 1 then
        collapse_root (Array.unsafe_get forest.forest_nodes 0)
      else make_strict_branch_node forest.forest_nodes

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
        if Array.length children = 0 then None
        else Some (make_strict_branch_node children)
      in
      (leaf, root)

let rec first_leaf_node = function
  | Empty -> invalid_index ()
  | Leaf values -> values
  | Branch branch -> first_leaf_node (Array.unsafe_get branch.children 0)

let rec remove_first_leaf_node = function
  | Empty | Leaf _ -> None
  | Branch branch ->
      let children =
        match remove_first_leaf_node (Array.unsafe_get branch.children 0) with
        | None -> Array.sub branch.children 1 (Array.length branch.children - 1)
        | Some child ->
            let children = Array.copy branch.children in
            Array.unsafe_set children 0 child;
            children
      in
      if Array.length children = 0 then None
      else Some (make_strict_branch_node children)

let root_or_empty = function
  | None -> Empty
  | Some root -> collapse_root root

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

let nth v index =
  match v with
  | Empty_vector -> invalid_index ()
  | Vector v ->
      if index < 0 || index >= v.count then invalid_index ();
      let head_length = Array.length v.head in
      if index < head_length then Array.unsafe_get v.head index
      else if index >= v.tailoff then
        Array.unsafe_get v.tail (index - v.tailoff)
      else get_node v.root (index - head_length)

let nth_opt v index =
  match v with
  | Empty_vector -> None
  | Vector v ->
      if index < 0 || index >= v.count then None
      else
        let head_length = Array.length v.head in
        if index < head_length then Some (Array.unsafe_get v.head index)
        else if index >= v.tailoff then
          Some (Array.unsafe_get v.tail (index - v.tailoff))
        else Some (get_node v.root (index - head_length))

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

let single_child_branch child =
  Branch
    {
      children = [| child |];
      sizes = None;
      count = node_count child;
      height = node_height child + 1;
    }

let node_full node =
  let capacity = capacity_for_height (node_height node) in
  capacity <> 0 && node_count node >= capacity

let node_full_at_height height node =
  let capacity = capacity_for_height height in
  capacity <> 0 && node_count node >= capacity

let rec new_path height leaf =
  if height = 0 then leaf else single_child_branch (new_path (height - 1) leaf)

let rec promote_to_height height node =
  if node_height node = height then node
  else promote_to_height height (single_child_branch node)

let rec rebalance_slice_children children =
  let length = Array.length children in
  let height = ref (node_height (Array.unsafe_get children 0)) in
  for index = 1 to length - 1 do
    height := max !height (node_height (Array.unsafe_get children index))
  done;
  for index = 0 to length - 1 do
    let child = Array.unsafe_get children index in
    if node_height child < !height then
      Array.unsafe_set children index (promote_to_height !height child)
  done;
  if !height = 0 then
    let branch = make_branch children in
    if length <= (node_count branch / width) + 3 then branch
    else
      make_branch
        (redistribute_concat_candidates children
           (concat_target_sizes children))
  else
    let flattened_length =
      Array.fold_left
        (fun total -> function
          | Branch branch -> total + Array.length branch.children
          | Empty | Leaf _ -> invalid_arg "expected promoted slice branch")
        0 children
    in
    if flattened_length > width then
      let children =
        if length <= (flattened_length / width) + 3 then children
        else
          redistribute_concat_candidates children
            (concat_target_sizes children)
      in
      make_branch children
    else
      let first =
        match Array.unsafe_get children 0 with
        | Branch branch -> Array.unsafe_get branch.children 0
        | Empty | Leaf _ -> invalid_arg "expected promoted slice branch"
      in
      let flattened = Array.make flattened_length first in
      let offset = ref 0 in
      Array.iter
        (function
          | Branch branch ->
              let length = Array.length branch.children in
              Array.blit branch.children 0 flattened !offset length;
              offset := !offset + length
          | Empty | Leaf _ -> invalid_arg "expected promoted slice branch")
        children;
      rebalance_slice_children flattened

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
  for index = start to Array.length sizes - 1 do
    Array.unsafe_set sizes' index (Array.unsafe_get sizes index + delta)
  done;
  sizes'

let replace_branch_child node child_index child delta =
  match node with
  | Branch branch ->
      let children = Array.copy branch.children in
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
            for index = 0 to length - 1 do
              Array.unsafe_set sizes' (index + 1)
                (child_count + Array.unsafe_get sizes index)
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

type 'a leaf_insert = {
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
  | Leaf _ -> make_strict_branch_node [| root; leaf |]
  | Branch _ ->
      let height = node_height root in
      if node_full root then
        make_strict_branch_node [| root; new_path height leaf |]
      else
        let result = { leaf_inserted = false; leaf_node = Empty } in
        insert_leaf result height root leaf (node_count leaf);
        if result.leaf_inserted then result.leaf_node
        else make_strict_branch_node [| root; result.leaf_node |]

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
  | Leaf _ -> make_strict_branch_node [| leaf; root |]
  | Branch _ ->
      let height = node_height root in
      if node_full root then
        make_strict_branch_node [| new_path height leaf; root |]
      else
        let result = { leaf_inserted = false; leaf_node = Empty } in
        insert_leaf_front result height root leaf (node_count leaf);
        if result.leaf_inserted then result.leaf_node
        else make_strict_branch_node [| result.leaf_node; root |]

let push_back v value =
  ensure_count_growth (length v) 1;
  match v with
  | Empty_vector -> make_with_edges [||] Empty [| value |]
  | Vector v ->
      let tail_length = Array.length v.tail in
      if tail_length < width then
        Vector
          {
            v with
            count = v.count + 1;
            tail = append_value v.tail value;
          }
      else
        let root = append_full_leaf v.root (Leaf v.tail) in
        Vector
          {
            count = v.count + 1;
            root;
            tail = [| value |];
            tailoff = Array.length v.head + node_count root;
            head = v.head;
          }

let set v index value =
  match v with
  | Empty_vector -> invalid_index ()
  | Vector v ->
      if index < 0 || index >= v.count then invalid_index ();
      let head_length = Array.length v.head in
      if index < head_length then (
        let head = Array.copy v.head in
        Array.unsafe_set head index value;
        Vector { v with head })
      else if index >= v.tailoff then (
        let tail = Array.copy v.tail in
        Array.unsafe_set tail (index - v.tailoff) value;
        Vector { v with tail })
      else
        make_with_edges v.head
          (set_node v.root (index - head_length) value)
          v.tail

let peek_back_vector v =
  let tail_length = Array.length v.tail in
  if tail_length > 0 then Array.unsafe_get v.tail (tail_length - 1)
  else if v.root <> Empty then get_node v.root (node_count v.root - 1)
  else
    let head_length = Array.length v.head in
    Array.unsafe_get v.head (head_length - 1)

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
  match v with
  | Empty_vector -> acc
  | Vector v ->
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
  match v with
  | Empty_vector -> acc
  | Vector v ->
      let acc = fold_array_right_range f v.tail 0 (Array.length v.tail) acc in
      let acc = fold_right_node f v.root acc in
      fold_array_right_range f v.head 0 (Array.length v.head) acc

let concat left right =
  ensure_count_growth (length left) (length right);
  match (left, right) with
  | Empty_vector, vector | vector, Empty_vector -> vector
  | Vector left, Vector right ->
      let root = concat_root (concat_middle_forest left right) in
      make_with_edges left.head root right.tail

let push_front v value =
  ensure_count_growth (length v) 1;
  match v with
  | Empty_vector -> make_with_edges [| value |] Empty [||]
  | Vector v ->
      let head_length = Array.length v.head in
      if head_length < width then
        Vector
          {
            v with
            count = v.count + 1;
            head = prepend_value v.head value;
            tailoff = v.tailoff + 1;
          }
      else
        let root = prepend_full_leaf v.root (Leaf v.head) in
        Vector
          {
            count = v.count + 1;
            root;
            tail = v.tail;
            tailoff = 1 + node_count root;
            head = [| value |];
          }

let peek_back = function
  | Empty_vector -> invalid_arg "empty vector"
  | Vector v -> peek_back_vector v

let peek_back_opt = function
  | Empty_vector -> None
  | Vector v -> Some (peek_back_vector v)

let peek_front_vector v =
  if Array.length v.head > 0 then Array.unsafe_get v.head 0
  else if v.root <> Empty then get_node v.root 0
  else Array.unsafe_get v.tail 0

let peek_front = function
  | Empty_vector -> invalid_arg "empty vector"
  | Vector v -> peek_front_vector v

let peek_front_opt = function
  | Empty_vector -> None
  | Vector v -> Some (peek_front_vector v)

let append = concat

let prepend = concat

let to_array v =
  match v with
  | Empty_vector -> [||]
  | Vector header ->
      let first = nth v 0 in
      let values = Array.make header.count first in
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
          make_strict_branch_node (Array.sub nodes start (stop - start)))
    in
    build_level parents

let root_of_full_chunks_rev chunks_rev =
  match chunks_rev with
  | [] -> Empty
  | first :: _ ->
      let leaf_count = List.length chunks_rev in
      let leaves = Array.make leaf_count (Leaf first) in
      let rec fill index = function
        | [] -> ()
        | chunk :: rest ->
            Array.unsafe_set leaves index (Leaf chunk);
            fill (index - 1) rest
      in
      fill (leaf_count - 1) chunks_rev;
      build_level leaves

let finish_nonempty_chunks chunks_rev chunk chunk_length =
  let tail =
    if chunk_length = width then chunk else Array.sub chunk 0 chunk_length
  in
  make_with_edges [||] (root_of_full_chunks_rev chunks_rev) tail

let of_list values =
  match values with
  | [] -> empty
  | first :: rest ->
      let first_chunk = Array.make width first in
      let rec loop chunks_rev chunk chunk_length = function
        | [] -> finish_nonempty_chunks chunks_rev chunk chunk_length
        | value :: rest ->
            if chunk_length = width then
              let next_chunk = Array.make width value in
              loop (chunk :: chunks_rev) next_chunk 1 rest
            else (
              Array.unsafe_set chunk chunk_length value;
              loop chunks_rev chunk (chunk_length + 1) rest)
      in
      loop [] first_chunk 1 rest

let of_seq values =
  match values () with
  | Seq.Nil -> empty
  | Seq.Cons (first, rest) ->
      let first_chunk = Array.make width first in
      let rec loop chunks_rev chunk chunk_length values =
        match values () with
        | Seq.Nil -> finish_nonempty_chunks chunks_rev chunk chunk_length
        | Seq.Cons (value, rest) ->
            if chunk_length = width then
              let next_chunk = Array.make width value in
              loop (chunk :: chunks_rev) next_chunk 1 rest
            else (
              Array.unsafe_set chunk chunk_length value;
              loop chunks_rev chunk (chunk_length + 1) rest)
      in
      loop [] first_chunk 1 rest

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

let array_slice values start stop =
  if start = 0 && stop = Array.length values then values
  else Array.sub values start (stop - start)

let rec slice_node node start stop =
  if start = stop then Empty
  else if start = 0 && stop = node_count node then node
  else
    match node with
    | Empty -> Empty
    | Leaf values -> Leaf (array_slice values start stop)
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
          let child_count = last_child - first_child + 1 in
          let children =
            Array.init child_count (fun child_offset ->
                let child_index = first_child + child_offset in
                let child = Array.unsafe_get branch.children child_index in
                let child_start =
                  if child_index = first_child then first_child_start
                  else
                    match branch.sizes with
                    | None -> radix_offset branch.height child_index
                    | Some sizes -> Array.unsafe_get sizes (child_index - 1)
                in
                let child_stop =
                  child_stop_offset branch.sizes branch.height branch.count
                    child_index
                in
                let child_slice_start =
                  if child_index = first_child then start - child_start else 0
                in
                let child_slice_stop =
                  if child_index = last_child then stop - child_start
                  else child_stop - child_start
                in
                let child =
                  if
                    child_slice_start = 0
                    && child_slice_stop = node_count child
                  then child
                  else slice_node child child_slice_start child_slice_stop
                in
                child)
          in
          rebalance_slice_children children

let slice_root node start stop = collapse_root (slice_node node start stop)

type 'a node_slice_with_edges = {
  sliced_head : 'a array;
  sliced_root : 'a node;
  sliced_tail : 'a array;
}

let rec leaf_at node index node_start =
  match node with
  | Empty -> invalid_index ()
  | Leaf values -> (values, node_start)
  | Branch branch ->
      let child_index, previous_size =
        child_range branch.sizes branch.height index
      in
      leaf_at
        (Array.unsafe_get branch.children child_index)
        (index - previous_size) (node_start + previous_size)

let slice_node_with_edges ~extract_head node start stop =
  let first_values, first_start = leaf_at node start 0 in
  let last_values, last_start = leaf_at node (stop - 1) 0 in
  if first_start = last_start then
    {
      sliced_head = [||];
      sliced_root = Empty;
      sliced_tail =
        array_slice first_values (start - first_start) (stop - first_start);
    }
  else
    let first_stop = first_start + Array.length first_values in
    let move_first_to_head =
      extract_head
      && (start > first_start || Array.length first_values < width)
    in
    let sliced_head =
      if move_first_to_head then
        array_slice first_values (start - first_start) (Array.length first_values)
      else [||]
    in
    let root_start = if move_first_to_head then first_stop else start in
    let sliced_root =
      if root_start = last_start then Empty
      else slice_root node root_start last_start
    in
    let sliced_tail = array_slice last_values 0 (stop - last_start) in
    { sliced_head; sliced_root; sliced_tail }

let subvec vector start stop =
  match vector with
  | Empty_vector ->
      if start = 0 && stop = 0 then Some empty else None
  | Vector v ->
      if start < 0 || stop < start || stop > v.count then None
      else
        let count = stop - start in
        if count = 0 then Some empty
        else if start = 0 && stop = v.count then Some vector
        else
          let head_length = Array.length v.head in
          let root_start = head_length in
          let root_stop = v.tailoff in
          let head =
            if start < head_length then
              array_slice v.head start (min stop head_length)
            else [||]
          in
          let slices_root = start < root_stop && stop > root_start in
          let slice_start = max start root_start - root_start in
          let slice_stop = min stop root_stop - root_start in
          let tail =
            if stop > v.tailoff then
              array_slice v.tail (max start v.tailoff - v.tailoff)
                (stop - v.tailoff)
            else [||]
          in
          let head, root, tail =
            if Array.length tail > 0 then
              let root =
                if slices_root then slice_root v.root slice_start slice_stop
                else Empty
              in
              (head, root, tail)
            else if slices_root then
              let sliced =
                slice_node_with_edges ~extract_head:(Array.length head = 0)
                  v.root slice_start slice_stop
              in
              let head =
                if Array.length head > 0 then head else sliced.sliced_head
              in
              (head, sliced.sliced_root, sliced.sliced_tail)
            else (head, Empty, [||])
          in
          Some (make_with_edges head root tail)

let pop_back v =
  match v with
  | Empty_vector -> None
  | Vector header ->
      let result =
        let tail_length = Array.length header.tail in
        if tail_length > 0 then
          let value = Array.unsafe_get header.tail (tail_length - 1) in
          if tail_length > 1 then
            ( value,
              Vector
                {
                  header with
                  count = header.count - 1;
                  tail = Array.sub header.tail 0 (tail_length - 1);
                } )
          else if header.root = Empty then
            ( value,
              vector_or_empty
                { header with count = header.count - 1; tail = [||] } )
          else
            let tail, root = take_last_leaf_node header.root in
            let root = root_or_empty root in
            ( value,
              vector_or_empty
                {
                  count = header.count - 1;
                  root;
                  tail;
                  tailoff = Array.length header.head + node_count root;
                  head = header.head;
                } )
        else if header.root = Empty then
          let head_length = Array.length header.head in
          let value = Array.unsafe_get header.head (head_length - 1) in
          if head_length = 1 then (value, empty)
          else
            ( value,
              Vector
                {
                  header with
                  count = header.count - 1;
                  head = Array.sub header.head 0 (head_length - 1);
                  tailoff = header.tailoff - 1;
                } )
        else
          let leaf, root = take_last_leaf_node header.root in
          let leaf_length = Array.length leaf in
          let value = Array.unsafe_get leaf (leaf_length - 1) in
          let root = root_or_empty root in
          let tail = Array.sub leaf 0 (leaf_length - 1) in
          let root, tail =
            if Array.length tail > 0 || root = Empty then (root, tail)
            else
              let tail, root = take_last_leaf_node root in
              (root_or_empty root, tail)
          in
          ( value,
            vector_or_empty
              {
                count = header.count - 1;
                root;
                tail;
                tailoff = Array.length header.head + node_count root;
                head = header.head;
              } )
      in
      Some result

let pop_front v =
  match v with
  | Empty_vector -> None
  | Vector header ->
      let result =
        let head_length = Array.length header.head in
        if head_length > 0 then
          let value = Array.unsafe_get header.head 0 in
          let head = Array.sub header.head 1 (head_length - 1) in
          ( value,
            vector_or_empty
              {
                header with
                count = header.count - 1;
                head;
                tailoff = header.tailoff - 1;
              } )
        else if header.root <> Empty then
          let leaf = first_leaf_node header.root in
          let value = Array.unsafe_get leaf 0 in
          let head = Array.sub leaf 1 (Array.length leaf - 1) in
          let root =
            remove_first_leaf_node header.root |> root_or_empty
          in
          ( value,
            vector_or_empty
              {
                count = header.count - 1;
                root;
                tail = header.tail;
                tailoff = Array.length head + node_count root;
                head;
              } )
        else
          let value = Array.unsafe_get header.tail 0 in
          let tail = Array.sub header.tail 1 (Array.length header.tail - 1) in
          ( value,
            vector_or_empty
              { header with count = header.count - 1; tail; tailoff = 0 } )
      in
      Some result

let rec map_node f = function
  | Empty -> Empty
  | Leaf values -> Leaf (Array.map f values)
  | Branch branch ->
      let children = Array.map (map_node f) branch.children in
      Branch { branch with children }

let map f v =
  match v with
  | Empty_vector -> empty
  | Vector v ->
      let head = Array.map f v.head in
      let root = map_node f v.root in
      let tail = Array.map f v.tail in
      Vector { v with root; tail; head }

let append_array v values =
  if Array.length values = 0 then v else concat v (of_array values)

let append_list v values =
  match values with
  | [] -> v
  | _ -> concat v (of_list values)

let prepend_list v values =
  match values with
  | [] -> v
  | _ -> prepend (of_list values) v

let prepend_array v values =
  if Array.length values = 0 then v else prepend (of_array values) v

let to_list v = fold_right (fun value acc -> value :: acc) v []

type 'a seq_frame = {
  seq_children : 'a node array;
  seq_next_child : int;
}

let rec seq_array values index rest () =
  if index = Array.length values then rest ()
  else
    Seq.Cons
      (Array.unsafe_get values index, seq_array values (index + 1) rest)

and seq_node node stack tail () =
  match node with
  | Empty -> seq_stack stack tail ()
  | Leaf values -> seq_array values 0 (seq_stack stack tail) ()
  | Branch branch ->
      let children = branch.children in
      let length = Array.length children in
      if length = 0 then seq_stack stack tail ()
      else
        let stack =
          if length = 1 then stack
          else { seq_children = children; seq_next_child = 1 } :: stack
        in
        seq_node (Array.unsafe_get children 0) stack tail ()

and seq_stack stack tail () =
  match stack with
  | [] -> seq_array tail 0 Seq.empty ()
  | frame :: rest ->
      let child =
        Array.unsafe_get frame.seq_children frame.seq_next_child
      in
      let seq_next_child = frame.seq_next_child + 1 in
      let stack =
        if seq_next_child = Array.length frame.seq_children then rest
        else { frame with seq_next_child } :: rest
      in
      seq_node child stack tail ()

let to_seq = function
  | Empty_vector -> Seq.empty
  | Vector v -> seq_array v.head 0 (seq_node v.root [] v.tail)

let reverse_array values =
  let length = Array.length values in
  if length = 0 then [||]
  else
    let reversed = Array.make length (Array.unsafe_get values (length - 1)) in
    for index = 0 to length - 1 do
      Array.unsafe_set reversed index
        (Array.unsafe_get values (length - 1 - index))
    done;
    reversed

let rec rev_node = function
  | Empty -> Empty
  | Leaf values -> Leaf (reverse_array values)
  | Branch branch ->
      let length = Array.length branch.children in
      let children = Array.make length Empty in
      for index = 0 to length - 1 do
        Array.unsafe_set children index
          (rev_node (Array.unsafe_get branch.children (length - 1 - index)))
      done;
      make_strict_branch_node children

let rev = function
  | Empty_vector -> empty
  | Vector v ->
      make_with_edges (reverse_array v.tail) (rev_node v.root)
        (reverse_array v.head)

let concat_map f v = fold_left (fun acc value -> concat acc (f value)) empty v

exception Predicate_found
exception Predicate_failed

let array_raise_exists p values =
  for index = 0 to Array.length values - 1 do
    if p (Array.unsafe_get values index) then raise Predicate_found
  done

let rec node_raise_exists p = function
  | Empty -> ()
  | Leaf values -> array_raise_exists p values
  | Branch branch ->
      let children = branch.children in
      for index = 0 to Array.length children - 1 do
        node_raise_exists p (Array.unsafe_get children index)
      done

let exists p v =
  match v with
  | Empty_vector -> false
  | Vector v ->
      (try
         array_raise_exists p v.head;
         node_raise_exists p v.root;
         array_raise_exists p v.tail;
         false
       with Predicate_found -> true)

let array_raise_for_all p values =
  for index = 0 to Array.length values - 1 do
    if not (p (Array.unsafe_get values index)) then raise Predicate_failed
  done

let rec node_raise_for_all p = function
  | Empty -> ()
  | Leaf values -> array_raise_for_all p values
  | Branch branch ->
      let children = branch.children in
      for index = 0 to Array.length children - 1 do
        node_raise_for_all p (Array.unsafe_get children index)
      done

let for_all p v =
  match v with
  | Empty_vector -> true
  | Vector v ->
      (try
         array_raise_for_all p v.head;
         node_raise_for_all p v.root;
         array_raise_for_all p v.tail;
         true
       with Predicate_failed -> false)

let array_raise_find p found values =
  for index = 0 to Array.length values - 1 do
    let value = Array.unsafe_get values index in
    if p value then found value
  done

let rec node_raise_find p found = function
  | Empty -> ()
  | Leaf values -> array_raise_find p found values
  | Branch branch ->
      let children = branch.children in
      for index = 0 to Array.length children - 1 do
        node_raise_find p found (Array.unsafe_get children index)
      done

let find_opt p v =
  match v with
  | Empty_vector -> None
  | Vector v ->
      let exception Found in
      let result = ref None in
      let found value =
        result := Some value;
        raise Found
      in
      (try
         array_raise_find p found v.head;
         node_raise_find p found v.root;
         array_raise_find p found v.tail;
         None
       with Found -> !result)

let find p v =
  match v with
  | Empty_vector -> raise Not_found
  | Vector v ->
      let exception Found in
      let result = ref None in
      let found value =
        result := Some value;
        raise Found
      in
      (try
         array_raise_find p found v.head;
         node_raise_find p found v.root;
         array_raise_find p found v.tail;
         raise Not_found
       with Found -> Option.get !result)

let iter_array f values =
  for index = 0 to Array.length values - 1 do
    f (Array.unsafe_get values index)
  done

let rec iter_node f = function
  | Empty -> ()
  | Leaf values -> iter_array f values
  | Branch branch ->
      let children = branch.children in
      for index = 0 to Array.length children - 1 do
        iter_node f (Array.unsafe_get children index)
      done

let iter f v =
  match v with
  | Empty_vector -> ()
  | Vector v ->
      iter_array f v.head;
      iter_node f v.root;
      iter_array f v.tail

let iteri_array f index values =
  let index = ref index in
  for offset = 0 to Array.length values - 1 do
    f !index (Array.unsafe_get values offset);
    incr index
  done;
  !index

let rec iteri_node f index = function
  | Empty -> index
  | Leaf values -> iteri_array f index values
  | Branch branch ->
      let index = ref index in
      let children = branch.children in
      for child_index = 0 to Array.length children - 1 do
        index := iteri_node f !index (Array.unsafe_get children child_index)
      done;
      !index

let iteri f v =
  match v with
  | Empty_vector -> ()
  | Vector v ->
      let index = iteri_array f 0 v.head in
      let index = iteri_node f index v.root in
      ignore (iteri_array f index v.tail)

let mapi_array f index values =
  let length = Array.length values in
  if length = 0 then [||]
  else
    let first = f !index (Array.unsafe_get values 0) in
    incr index;
    let mapped = Array.make length first in
    for offset = 1 to length - 1 do
      Array.unsafe_set mapped offset
        (f !index (Array.unsafe_get values offset));
      incr index
    done;
    mapped

let rec mapi_node f index = function
  | Empty -> Empty
  | Leaf values -> Leaf (mapi_array f index values)
  | Branch branch ->
      let children_length = Array.length branch.children in
      let first = mapi_node f index (Array.unsafe_get branch.children 0) in
      let children = Array.make children_length first in
      for child_index = 1 to children_length - 1 do
        Array.unsafe_set children child_index
          (mapi_node f index (Array.unsafe_get branch.children child_index))
      done;
      Branch { branch with children }

let mapi f v =
  match v with
  | Empty_vector -> empty
  | Vector v ->
      let index = ref 0 in
      let head = mapi_array f index v.head in
      let root = mapi_node f index v.root in
      let tail = mapi_array f index v.tail in
      Vector { count = v.count; root; tail; tailoff = v.tailoff; head }

let find_map f v =
  let exception Found in
  let result = ref None in
  try
    iter
      (fun value ->
        match f value with
        | None -> ()
        | Some value ->
            result := Some value;
            raise Found)
      v;
    None
  with Found -> !result

let mem value v = exists (( = ) value) v

type cursor_phase = Root | Root_rest | Done

type 'a leaf_cursor = {
  cursor_root : 'a node;
  cursor_final : 'a array;
  cursor_children : 'a node array array;
  cursor_next_child : int array;
  mutable cursor_depth : int;
  mutable cursor_phase : cursor_phase;
  mutable cursor_values : 'a array;
  mutable cursor_index : int;
}

let make_leaf_cursor v =
  let stack_size = max 0 (node_height v.root) in
  {
    cursor_root = v.root;
    cursor_final = v.tail;
    cursor_children = Array.make stack_size [||];
    cursor_next_child = Array.make stack_size 0;
    cursor_depth = 0;
    cursor_phase = Root;
    cursor_values = v.head;
    cursor_index = 0;
  }

let make_reverse_leaf_cursor v =
  let stack_size = max 0 (node_height v.root) in
  {
    cursor_root = v.root;
    cursor_final = v.head;
    cursor_children = Array.make stack_size [||];
    cursor_next_child = Array.make stack_size 0;
    cursor_depth = 0;
    cursor_phase = Root;
    cursor_values = v.tail;
    cursor_index = Array.length v.tail - 1;
  }

(* Keep forward and reverse operations separate so forward pairwise traversal
   does not branch on direction at each leaf boundary. *)
let cursor_set_values cursor values =
  cursor.cursor_values <- values;
  cursor.cursor_index <- 0

let reverse_cursor_set_values cursor values =
  cursor.cursor_values <- values;
  cursor.cursor_index <- Array.length values - 1

let rec cursor_descend cursor = function
  | Empty -> false
  | Leaf values ->
      cursor_set_values cursor values;
      true
  | Branch branch ->
      let depth = cursor.cursor_depth in
      Array.unsafe_set cursor.cursor_children depth branch.children;
      Array.unsafe_set cursor.cursor_next_child depth 1;
      cursor.cursor_depth <- depth + 1;
      cursor_descend cursor (Array.unsafe_get branch.children 0)

let rec reverse_cursor_descend cursor = function
  | Empty -> false
  | Leaf values ->
      reverse_cursor_set_values cursor values;
      true
  | Branch branch ->
      let depth = cursor.cursor_depth in
      let child_index = Array.length branch.children - 1 in
      Array.unsafe_set cursor.cursor_children depth branch.children;
      Array.unsafe_set cursor.cursor_next_child depth (child_index - 1);
      cursor.cursor_depth <- depth + 1;
      reverse_cursor_descend cursor
        (Array.unsafe_get branch.children child_index)

let rec cursor_next_root_leaf cursor =
  let depth = cursor.cursor_depth in
  if depth = 0 then false
  else
    let level = depth - 1 in
    let children = Array.unsafe_get cursor.cursor_children level in
    let child_index = Array.unsafe_get cursor.cursor_next_child level in
    if child_index = Array.length children then (
      cursor.cursor_depth <- level;
      cursor_next_root_leaf cursor)
    else (
      Array.unsafe_set cursor.cursor_next_child level (child_index + 1);
      cursor_descend cursor (Array.unsafe_get children child_index))

let rec reverse_cursor_next_root_leaf cursor =
  let depth = cursor.cursor_depth in
  if depth = 0 then false
  else
    let level = depth - 1 in
    let children = Array.unsafe_get cursor.cursor_children level in
    let child_index = Array.unsafe_get cursor.cursor_next_child level in
    if child_index < 0 then (
      cursor.cursor_depth <- level;
      reverse_cursor_next_root_leaf cursor)
    else (
      Array.unsafe_set cursor.cursor_next_child level (child_index - 1);
      reverse_cursor_descend cursor (Array.unsafe_get children child_index))

let rec cursor_advance cursor =
  match cursor.cursor_phase with
  | Root ->
      cursor.cursor_phase <- Root_rest;
      if cursor_descend cursor cursor.cursor_root then true
      else cursor_advance cursor
  | Root_rest ->
      if cursor_next_root_leaf cursor then true
      else (
        cursor.cursor_phase <- Done;
        if Array.length cursor.cursor_final = 0 then false
        else (
          cursor_set_values cursor cursor.cursor_final;
          true))
  | Done -> false

let rec reverse_cursor_advance cursor =
  match cursor.cursor_phase with
  | Root ->
      cursor.cursor_phase <- Root_rest;
      if reverse_cursor_descend cursor cursor.cursor_root then true
      else reverse_cursor_advance cursor
  | Root_rest ->
      if reverse_cursor_next_root_leaf cursor then true
      else (
        cursor.cursor_phase <- Done;
        if Array.length cursor.cursor_final = 0 then false
        else (
          reverse_cursor_set_values cursor cursor.cursor_final;
          true))
  | Done -> false

let cursor_ensure_values cursor =
  cursor.cursor_index < Array.length cursor.cursor_values
  || cursor_advance cursor

let reverse_cursor_ensure_values cursor =
  cursor.cursor_index >= 0 || reverse_cursor_advance cursor

let cursor_available cursor =
  Array.length cursor.cursor_values - cursor.cursor_index

let reverse_cursor_available cursor = cursor.cursor_index + 1

let cursor_move cursor count =
  cursor.cursor_index <- cursor.cursor_index + count

let reverse_cursor_move cursor count =
  cursor.cursor_index <- cursor.cursor_index - count

let cursor_common_chunk_length left right remaining =
  ignore (cursor_ensure_values left);
  ignore (cursor_ensure_values right);
  let left_available = cursor_available left in
  let right_available = cursor_available right in
  min remaining (min left_available right_available)

let reverse_cursor_common_chunk_length left right remaining =
  ignore (reverse_cursor_ensure_values left);
  ignore (reverse_cursor_ensure_values right);
  let left_available = reverse_cursor_available left in
  let right_available = reverse_cursor_available right in
  min remaining (min left_available right_available)

let rec for_all2_array_range predicate left left_index right right_index count =
  count = 0
  ||
  (predicate
     (Array.unsafe_get left left_index)
     (Array.unsafe_get right right_index)
  && for_all2_array_range predicate left (left_index + 1) right
       (right_index + 1) (count - 1))

let equal equal_value left right =
  let count = length left in
  if count <> length right then false
  else
    match (left, right) with
    | Empty_vector, Empty_vector -> true
    | Vector left, Vector right ->
        let left = make_leaf_cursor left in
        let right = make_leaf_cursor right in
        let rec loop remaining =
          if remaining = 0 then true
          else
            let count = cursor_common_chunk_length left right remaining in
            if
              for_all2_array_range equal_value left.cursor_values
                left.cursor_index right.cursor_values right.cursor_index count
            then (
              left.cursor_index <- left.cursor_index + count;
              right.cursor_index <- right.cursor_index + count;
              loop (remaining - count))
            else false
        in
        loop count
    | Empty_vector, Vector _ | Vector _, Empty_vector ->
        invalid_arg "Rrbvec.equal: inconsistent empty vector"

let rec compare_array_range compare_value left left_index right right_index count =
  if count = 0 then 0
  else
    let order =
      compare_value
        (Array.unsafe_get left left_index)
        (Array.unsafe_get right right_index)
    in
    if order = 0 then
      compare_array_range compare_value left (left_index + 1) right
        (right_index + 1) (count - 1)
    else order

let compare compare_value left right =
  let left_count = length left in
  let right_count = length right in
  let common_count = min left_count right_count in
  if common_count = 0 then Int.compare left_count right_count
  else
    match (left, right) with
    | Vector left, Vector right ->
        let left = make_leaf_cursor left in
        let right = make_leaf_cursor right in
        let rec loop remaining =
          if remaining = 0 then Int.compare left_count right_count
          else
            let count = cursor_common_chunk_length left right remaining in
            let order =
              compare_array_range compare_value left.cursor_values
                left.cursor_index right.cursor_values right.cursor_index count
            in
            if order = 0 then (
              left.cursor_index <- left.cursor_index + count;
              right.cursor_index <- right.cursor_index + count;
              loop (remaining - count))
            else order
        in
        loop common_count
    | Empty_vector, Empty_vector
    | Empty_vector, Vector _
    | Vector _, Empty_vector ->
        invalid_arg "Rrbvec.compare: inconsistent empty vector"

let pairwise_count name left right =
  let count = length left in
  if count <> length right then invalid_arg name;
  count

let make_pair_cursors left right =
  match (left, right) with
  | Vector left, Vector right ->
      (make_leaf_cursor left, make_leaf_cursor right)
  | Empty_vector, Empty_vector
  | Empty_vector, Vector _
  | Vector _, Empty_vector -> invalid_arg "expected two non-empty vectors"

let make_reverse_pair_cursors left right =
  match (left, right) with
  | Vector left, Vector right ->
      (make_reverse_leaf_cursor left, make_reverse_leaf_cursor right)
  | Empty_vector, Empty_vector
  | Empty_vector, Vector _
  | Vector _, Empty_vector -> invalid_arg "expected two non-empty vectors"

let iter2_array f left left_index right right_index count =
  for offset = 0 to count - 1 do
    f
      (Array.unsafe_get left (left_index + offset))
      (Array.unsafe_get right (right_index + offset))
  done

let iter2 f left right =
  let count = pairwise_count "Rrbvec.iter2" left right in
  if count > 0 then
    let left, right = make_pair_cursors left right in
    let rec loop remaining =
      if remaining > 0 then (
        let count = cursor_common_chunk_length left right remaining in
        iter2_array f left.cursor_values left.cursor_index right.cursor_values
          right.cursor_index count;
        cursor_move left count;
        cursor_move right count;
        loop (remaining - count))
    in
    loop count

let fold_left2_array f acc left left_index right right_index count =
  let acc = ref acc in
  for offset = 0 to count - 1 do
    acc :=
      f !acc
        (Array.unsafe_get left (left_index + offset))
        (Array.unsafe_get right (right_index + offset))
  done;
  !acc

let fold_left2 f acc left right =
  let count = pairwise_count "Rrbvec.fold_left2" left right in
  if count = 0 then acc
  else
    let left, right = make_pair_cursors left right in
    let rec loop acc remaining =
      if remaining = 0 then acc
      else
        let count = cursor_common_chunk_length left right remaining in
        let acc =
          fold_left2_array f acc left.cursor_values left.cursor_index
            right.cursor_values right.cursor_index count
        in
        cursor_move left count;
        cursor_move right count;
        loop acc (remaining - count)
    in
    loop acc count

let for_all2 predicate left right =
  let count = pairwise_count "Rrbvec.for_all2" left right in
  if count = 0 then true
  else
    let left, right = make_pair_cursors left right in
    let rec loop remaining =
      if remaining = 0 then true
      else
        let count = cursor_common_chunk_length left right remaining in
        if
          for_all2_array_range predicate left.cursor_values left.cursor_index
            right.cursor_values right.cursor_index count
        then (
          cursor_move left count;
          cursor_move right count;
          loop (remaining - count))
        else false
    in
    loop count

let rec exists2_array_range predicate left left_index right right_index count =
  count > 0
  &&
  (predicate
     (Array.unsafe_get left left_index)
     (Array.unsafe_get right right_index)
  || exists2_array_range predicate left (left_index + 1) right
       (right_index + 1) (count - 1))

let exists2 predicate left right =
  let count = pairwise_count "Rrbvec.exists2" left right in
  if count = 0 then false
  else
    let left, right = make_pair_cursors left right in
    let rec loop remaining =
      if remaining = 0 then false
      else
        let count = cursor_common_chunk_length left right remaining in
        if
          exists2_array_range predicate left.cursor_values left.cursor_index
            right.cursor_values right.cursor_index count
        then true
        else (
          cursor_move left count;
          cursor_move right count;
          loop (remaining - count))
    in
    loop count

let fold_right2_array f left left_index right right_index count acc =
  let acc = ref acc in
  for offset = 0 to count - 1 do
    acc :=
      f
        (Array.unsafe_get left (left_index - offset))
        (Array.unsafe_get right (right_index - offset))
        !acc
  done;
  !acc

let fold_right2 f left right acc =
  let count = pairwise_count "Rrbvec.fold_right2" left right in
  if count = 0 then acc
  else
    let left, right = make_reverse_pair_cursors left right in
    let rec loop acc remaining =
      if remaining = 0 then acc
      else
        let count =
          reverse_cursor_common_chunk_length left right remaining
        in
        let acc =
          fold_right2_array f left.cursor_values left.cursor_index
            right.cursor_values right.cursor_index count acc
        in
        reverse_cursor_move left count;
        reverse_cursor_move right count;
        loop acc (remaining - count)
    in
    loop acc count

let assoc ?cmp key bindings =
  match cmp with
  | None -> snd (find (fun (candidate, _) -> candidate = key) bindings)
  | Some cmp ->
      snd (find (fun (candidate, _) -> cmp candidate key = 0) bindings)

let assoc_opt ?cmp key bindings =
  match cmp with
  | None ->
      find_map
        (fun (candidate, value) ->
          if candidate = key then Some value else None)
        bindings
  | Some cmp ->
      find_map
        (fun (candidate, value) ->
          if cmp candidate key = 0 then Some value else None)
        bindings

let mem_assoc ?cmp key bindings =
  match cmp with
  | None -> exists (fun (candidate, _) -> candidate = key) bindings
  | Some cmp -> exists (fun (candidate, _) -> cmp candidate key = 0) bindings

let remove_assoc ?cmp key bindings =
  match cmp with
  | None ->
      snd
        (fold_left
           (fun (removed, result) ((candidate, _) as binding) ->
             if (not removed) && candidate = key then (true, result)
             else (removed, push_back result binding))
           (false, empty) bindings)
  | Some cmp ->
      snd
        (fold_left
           (fun (removed, result) ((candidate, _) as binding) ->
             if (not removed) && cmp candidate key = 0 then (true, result)
             else (removed, push_back result binding))
           (false, empty) bindings)

let init_array length start f =
  if length = 0 then [||]
  else
    let first = f start in
    let values = Array.make length first in
    for offset = 1 to length - 1 do
      Array.unsafe_set values offset (f (start + offset))
    done;
    values

let init length f =
  if length < 0 then invalid_arg "Rrbvec.init";
  if length = 0 then empty
  else if length <= width then
    make_with_edges [||] Empty (init_array length 0 f)
  else
    let tail_length =
      let remainder = length mod width in
      if remainder = 0 then width else remainder
    in
    let root_count = length - tail_length in
    let leaf_count = root_count / width in
    let first_leaf = Leaf (init_array width 0 f) in
    let leaves = Array.make leaf_count first_leaf in
    for leaf_index = 1 to leaf_count - 1 do
      Array.unsafe_set leaves leaf_index
        (Leaf (init_array width (leaf_index * width) f))
    done;
    let tail = init_array tail_length root_count f in
    make_with_edges [||] (build_level leaves) tail

let sort compare v = of_list (List.sort compare (to_list v))

let sort_uniq compare v = of_list (List.sort_uniq compare (to_list v))

type 'a chunk_sink = {
  mutable sink_chunks_rev : 'a array list;
  mutable sink_chunk : 'a array option;
  mutable sink_chunk_length : int;
}

let create_chunk_sink () =
  { sink_chunks_rev = []; sink_chunk = None; sink_chunk_length = 0 }

let chunk_sink_add sink value =
  match sink.sink_chunk with
  | None ->
      sink.sink_chunk <- Some (Array.make width value);
      sink.sink_chunk_length <- 1
  | Some chunk when sink.sink_chunk_length = width ->
      sink.sink_chunks_rev <- chunk :: sink.sink_chunks_rev;
      sink.sink_chunk <- Some (Array.make width value);
      sink.sink_chunk_length <- 1
  | Some chunk ->
      Array.unsafe_set chunk sink.sink_chunk_length value;
      sink.sink_chunk_length <- sink.sink_chunk_length + 1

let chunk_sink_result sink =
  match sink.sink_chunk with
  | None -> empty
  | Some chunk ->
      finish_nonempty_chunks sink.sink_chunks_rev chunk sink.sink_chunk_length

let map2_array f sink left left_index right right_index count =
  for offset = 0 to count - 1 do
    chunk_sink_add sink
      (f
         (Array.unsafe_get left (left_index + offset))
         (Array.unsafe_get right (right_index + offset)))
  done

let map2 f left right =
  let count = pairwise_count "Rrbvec.map2" left right in
  if count = 0 then empty
  else
    let left, right = make_pair_cursors left right in
    let sink = create_chunk_sink () in
    let rec loop remaining =
      if remaining = 0 then chunk_sink_result sink
      else
        let count = cursor_common_chunk_length left right remaining in
        map2_array f sink left.cursor_values left.cursor_index
          right.cursor_values right.cursor_index count;
        cursor_move left count;
        cursor_move right count;
        loop (remaining - count)
    in
    loop count

let combine left right = map2 (fun left right -> (left, right)) left right

let filter_array p sink values =
  for index = 0 to Array.length values - 1 do
    let value = Array.unsafe_get values index in
    if p value then chunk_sink_add sink value
  done

let rec filter_node p sink = function
  | Empty -> ()
  | Leaf values -> filter_array p sink values
  | Branch branch ->
      let children = branch.children in
      for index = 0 to Array.length children - 1 do
        filter_node p sink (Array.unsafe_get children index)
      done

let filter p v =
  match v with
  | Empty_vector -> empty
  | Vector v ->
      let sink = create_chunk_sink () in
      filter_array p sink v.head;
      filter_node p sink v.root;
      filter_array p sink v.tail;
      chunk_sink_result sink

let filter_map_array f sink values =
  for index = 0 to Array.length values - 1 do
    match f (Array.unsafe_get values index) with
    | None -> ()
    | Some value -> chunk_sink_add sink value
  done

let rec filter_map_node f sink = function
  | Empty -> ()
  | Leaf values -> filter_map_array f sink values
  | Branch branch ->
      let children = branch.children in
      for index = 0 to Array.length children - 1 do
        filter_map_node f sink (Array.unsafe_get children index)
      done

let filter_map f v =
  match v with
  | Empty_vector -> empty
  | Vector v ->
      let sink = create_chunk_sink () in
      filter_map_array f sink v.head;
      filter_map_node f sink v.root;
      filter_map_array f sink v.tail;
      chunk_sink_result sink

let partition_array p left right values =
  for index = 0 to Array.length values - 1 do
    let value = Array.unsafe_get values index in
    if p value then chunk_sink_add left value else chunk_sink_add right value
  done

let rec partition_node p left right = function
  | Empty -> ()
  | Leaf values -> partition_array p left right values
  | Branch branch ->
      let children = branch.children in
      for index = 0 to Array.length children - 1 do
        partition_node p left right (Array.unsafe_get children index)
      done

let partition p v =
  match v with
  | Empty_vector -> (empty, empty)
  | Vector v ->
      let left = create_chunk_sink () in
      let right = create_chunk_sink () in
      partition_array p left right v.head;
      partition_node p left right v.root;
      partition_array p left right v.tail;
      (chunk_sink_result left, chunk_sink_result right)

module Private = struct
  (*
    Internal invariants checked by [invariants]:

    - The empty vector has one canonical [Empty_vector] representation.
    - [Vector] headers have positive [count].
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
    - Root height stays within the Scala Quick logarithmic bound.
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
    let quick_extras = 2 in
    let minimum_branching = width - quick_extras - 1 in
    let bound =
      max_height_for_count ~base:minimum_branching (max 1 v.tailoff) + 1
    in
    require "vector"
      (root_height <= bound)
      "height bound exceeded: root height %d must be <= %d" root_height bound

  let check_vector_header ?(strict = false) v =
    require "vector" (v.count > 0) "Vector count must be positive, got %d"
      v.count;
    let root_count, root_height, _root_leaves = check_node true "root" v.root in
    (match v.root with
    | Empty ->
        require "vector" (root_count = 0) "empty root must have zero count"
    | Leaf _ -> require "vector" (root_count > 0) "leaf root must be non-empty"
    | Branch branch ->
        require "root"
          (Array.length branch.children > 1)
          "root branch must have more than one child";
        require "vector" (root_count > 0) "branch root must be non-empty");
    require "vector"
      (v.root <> Empty || Array.length v.head > 0 || Array.length v.tail > 0)
      "non-empty vector must contain a root, head, or tail segment";
    check_tail v root_count;
    check_height_bound v root_height;
    if strict && is_leftwise_dense v.root && v.root <> Empty then
      require "root"
        (rightmost_leaf_length v.root = width)
        "rightmost leaf length must be width for a non-empty leftwise-dense root"

  let check_vector ?strict = function
    | Empty_vector -> ()
    | Vector v -> check_vector_header ?strict v

  let invariants v = check_vector v
end
