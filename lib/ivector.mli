type 'a t

val empty : 'a t

val length : 'a t -> int

val is_empty : 'a t -> bool

val get : 'a t -> int -> 'a

val set : 'a t -> int -> 'a -> 'a t

val push : 'a t -> 'a -> 'a t

val pop : 'a t -> 'a t

val peek : 'a t -> 'a

val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc

val map : ('a -> 'b) -> 'a t -> 'b t

val subvec : 'a t -> int -> int -> 'a t

val concat : 'a t -> 'a t -> 'a t

val of_list : 'a list -> 'a t

val to_list : 'a t -> 'a list

val of_array : 'a array -> 'a t

val to_array : 'a t -> 'a array

val of_seq : 'a Seq.t -> 'a t

val to_seq : 'a t -> 'a Seq.t
