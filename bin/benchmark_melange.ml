let make_indices count modulo_by =
  Array.init count (fun i -> ((i * 1_103) + 12_345) mod modulo_by)

let range_sum start length = (start + start + length - 1) * length / 2

let build_back size =
  let rec loop i values =
    if i = size then values else loop (i + 1) (Rrbvec.push_back values i)
  in
  loop 0 Rrbvec.empty

let build_front size =
  let rec loop i values =
    if i = size then values else loop (i + 1) (Rrbvec.push_front values i)
  in
  loop 0 Rrbvec.empty

let sum values = Rrbvec.fold_left ( + ) 0 values

let fold_ignore values = Rrbvec.fold_left (fun _ value -> value) 0 values

let random_read values count =
  let indices = make_indices count (Rrbvec.length values) in
  Array.fold_left (fun acc index -> acc + Rrbvec.get values index) 0 indices

let random_write values count =
  let indices = make_indices count (Rrbvec.length values) in
  Array.fold_left
    (fun values (update_index, value_index) ->
      Rrbvec.set values value_index (-(update_index + 1)))
    values
    (Array.mapi (fun update_index value_index -> (update_index, value_index)) indices)

let map_values values = Rrbvec.map (fun value -> (value * 2) + 1) values

let repeated_subvec values steps =
  let rec loop steps values =
    if steps = 0 then values
    else
      let length = Rrbvec.length values in
      loop (steps - 1) (Rrbvec.subvec values 1 (length - 1))
  in
  loop steps values

let chunk_bounds size chunks =
  let base = size / chunks in
  let remainder = size mod chunks in
  Array.init chunks (fun index ->
      let extra = if index < remainder then 1 else 0 in
      let start = (index * base) + min index remainder in
      (start, base + extra))

let build_chunks values chunks =
  let bounds = chunk_bounds (Rrbvec.length values) chunks in
  Array.map
    (fun (start, length) -> Rrbvec.subvec values start (start + length))
    bounds

let concat_built_chunks chunks =
  let first = Array.unsafe_get chunks 0 in
  let result = ref first in
  for i = 1 to Array.length chunks - 1 do
    result := Rrbvec.concat !result (Array.unsafe_get chunks i)
  done;
  !result

let concat_chunks values chunks =
  let bounds = chunk_bounds (Rrbvec.length values) chunks in
  let first_start, first_length = Array.unsafe_get bounds 0 in
  let first = Rrbvec.subvec values first_start (first_start + first_length) in
  let result = ref first in
  for i = 1 to Array.length bounds - 1 do
    let start, length = Array.unsafe_get bounds i in
    result := Rrbvec.concat !result (Rrbvec.subvec values start (start + length))
  done;
  !result

let pop_back_all values =
  let rec loop values =
    if Rrbvec.is_empty values then values else loop (snd (Rrbvec.pop_back values))
  in
  loop values

let pop_front_all values =
  let rec loop values =
    if Rrbvec.is_empty values then values else loop (snd (Rrbvec.pop_front values))
  in
  loop values

let push_pop size = pop_back_all (build_back size)

let set_api name fn api = Js.Dict.set api name (Obj.magic fn)

let set_global : string -> Obj.t -> unit =
  [%raw {|function(name, value) { globalThis[name] = value; }|}]

let () =
  let api = Js.Dict.empty () in
  set_api "buildBack" build_back api;
  set_api "buildFront" build_front api;
  set_api "length" Rrbvec.length api;
  set_api "sum" sum api;
  set_api "foldIgnore" fold_ignore api;
  set_api "randomRead" random_read api;
  set_api "randomWrite" random_write api;
  set_api "mapValues" map_values api;
  set_api "repeatedSubvec" repeated_subvec api;
  set_api "buildChunks" build_chunks api;
  set_api "concatBuiltChunks" concat_built_chunks api;
  set_api "concatChunks" concat_chunks api;
  set_api "popBackAll" pop_back_all api;
  set_api "popFrontAll" pop_front_all api;
  set_api "pushPop" push_pop api;
  set_api "rangeSum" range_sum api;
  set_global "rrbvecMelange" (Obj.magic api)
