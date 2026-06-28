let bits = 5
let width = 1 lsl bits
let mask = width - 1

type 'a node =
  | Empty
  | Branch of 'a node option array
  | Leaf of 'a array

type 'a t = {
  count : int;
  shift : int;
  root : 'a node;
  tail : 'a array;
  tailoff : int;
}

let empty = { count = 0; shift = bits; root = Empty; tail = [||]; tailoff = 0 }

let length v = v.count

let is_empty v = v.count = 0

let slot index level = (index lsr level) land mask

let tailoff count =
  if count < width then 0 else ((count - 1) lsr bits) lsl bits

let invalid_index () = invalid_arg "index out of bounds"

let rec array_for_node index level node =
  match node with
  | Empty -> invalid_arg "corrupt vector"
  | Leaf values -> values
  | Branch children -> (
      match children.(slot index level) with
      | None -> invalid_arg "corrupt vector"
      | Some child -> array_for_node index (level - bits) child)

let rec array_for v index =
  if index < 0 || index >= v.count then invalid_index ();
  if index >= v.tailoff then v.tail
  else array_for_node index v.shift v.root

let get v index =
  let values = array_for v index in
  values.(index land mask)

let rec do_assoc level node index value =
  match node with
  | Empty -> invalid_arg "corrupt vector"
  | Leaf values ->
      let values' = Array.copy values in
      values'.(index land mask) <- value;
      Leaf values'
  | Branch children ->
      let children' = Array.copy children in
      let i = slot index level in
      let child =
        match children.(i) with
        | Some child -> child
        | None -> invalid_arg "corrupt vector"
      in
      children'.(i) <- Some (do_assoc (level - bits) child index value);
      Branch children'

let rec new_path level leaf =
  if level = 0 then leaf
  else
    let children = Array.make width None in
    children.(0) <- Some (new_path (level - bits) leaf);
    Branch children

let rec push_tail count level parent tail_leaf =
  let children =
    match parent with
    | Empty -> Array.make width None
    | Branch children -> Array.copy children
    | Leaf _ -> invalid_arg "corrupt vector"
  in
  let subidx = slot (count - 1) level in
  let child =
    if level = bits then tail_leaf
    else
      match children.(subidx) with
      | Some child -> push_tail count (level - bits) child tail_leaf
      | None -> new_path (level - bits) tail_leaf
  in
  children.(subidx) <- Some child;
  Branch children

let append_tail tail value =
  let length = Array.length tail in
  let tail' = Array.make (length + 1) value in
  Array.blit tail 0 tail' 0 length;
  tail'

let push v value =
  let count = v.count + 1 in
  if Array.length v.tail < width then
    { v with count; tail = append_tail v.tail value; tailoff = tailoff count }
  else
    let tail_leaf = Leaf v.tail in
    let root, shift =
      if (v.count lsr bits) > (1 lsl v.shift) then
        let children = Array.make width None in
        children.(0) <- Some v.root;
        children.(1) <- Some (new_path v.shift tail_leaf);
        (Branch children, v.shift + bits)
      else (push_tail v.count v.shift v.root tail_leaf, v.shift)
    in
    { count; shift; root; tail = [| value |]; tailoff = tailoff count }

let set v index value =
  if index < 0 || index > v.count then invalid_index ();
  if index = v.count then push v value
  else if index >= v.tailoff then (
    let tail = Array.copy v.tail in
    tail.(index land mask) <- value;
    { v with tail })
  else { v with root = do_assoc v.shift v.root index value }

let peek v =
  if v.count = 0 then invalid_index ();
  v.tail.((v.count - 1) land mask)

let rec pop_tail count level node =
  match node with
  | Empty -> None
  | Leaf _ -> invalid_arg "corrupt vector"
  | Branch children ->
      let subidx = slot (count - 2) level in
      if level > bits then (
        let child =
          match children.(subidx) with
          | Some child -> child
          | None -> invalid_arg "corrupt vector"
        in
        match pop_tail count (level - bits) child with
        | None when subidx = 0 -> None
        | new_child ->
            let children' = Array.copy children in
            children'.(subidx) <- new_child;
            Some (Branch children'))
      else if subidx = 0 then None
      else
        let children' = Array.copy children in
        children'.(subidx) <- None;
        Some (Branch children')

let pop v =
  if v.count = 0 then invalid_index ()
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
      | Branch children when v.shift > bits && children.(1) = None -> (
          match children.(0) with
          | Some child -> (child, v.shift - bits)
          | None -> (Empty, bits))
      | _ -> (root, v.shift)
    in
    { count; shift; root; tail = new_tail; tailoff = tailoff count }

let of_list values = List.fold_left push empty values

let to_list v = List.init v.count (get v)
