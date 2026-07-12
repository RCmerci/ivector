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

let nth values index = Rrbvec.nth values index

let subvec values start stop =
  match Rrbvec.subvec values start stop with
  | Some values -> values
  | None -> invalid_arg "Rrbvec.subvec returned None"

let pop_back values =
  match Rrbvec.pop_back values with
  | Some result -> result
  | None -> invalid_arg "Rrbvec.pop_back returned None"

let pop_front values =
  match Rrbvec.pop_front values with
  | Some result -> result
  | None -> invalid_arg "Rrbvec.pop_front returned None"

let random_read values count =
  let indices = make_indices count (Rrbvec.length values) in
  Array.fold_left (fun acc index -> acc + nth values index) 0 indices

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
      loop (steps - 1) (subvec values 1 (length - 1))
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
    (fun (start, length) -> subvec values start (start + length))
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
  let first = subvec values first_start (first_start + first_length) in
  let result = ref first in
  for i = 1 to Array.length bounds - 1 do
    let start, length = Array.unsafe_get bounds i in
    result := Rrbvec.concat !result (subvec values start (start + length))
  done;
  !result

let pop_back_all values =
  let rec loop values =
    if Rrbvec.is_empty values then values else loop (snd (pop_back values))
  in
  loop values

let pop_front_all values =
  let rec loop values =
    if Rrbvec.is_empty values then values else loop (snd (pop_front values))
  in
  loop values

let push_pop size = pop_back_all (build_back size)

let concat_map_singleton values = Rrbvec.concat_map Rrbvec.singleton values

let concat_map_pair values =
  Rrbvec.concat_map (fun value -> Rrbvec.of_array [| value; -value |]) values

let concat_map_mostly_empty values =
  Rrbvec.concat_map
    (fun value -> if value mod 10 = 0 then Rrbvec.singleton value else Rrbvec.empty)
    values

let concat_map_constant values mapped =
  Rrbvec.concat_map (fun _ -> mapped) values

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
  set_api "concatMapSingleton" concat_map_singleton api;
  set_api "concatMapPair" concat_map_pair api;
  set_api "concatMapMostlyEmpty" concat_map_mostly_empty api;
  set_api "concatMapConstant" concat_map_constant api;
  set_api "rangeSum" range_sum api;
  set_global "rrbvecMelange" (Obj.magic api)
