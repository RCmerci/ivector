type 'a t

val empty : 'a t

val length : 'a t -> int

val is_empty : 'a t -> bool

val get : 'a t -> int -> 'a

val set : 'a t -> int -> 'a -> 'a t

val push : 'a t -> 'a -> 'a t

val pop : 'a t -> 'a t

val peek : 'a t -> 'a

val of_list : 'a list -> 'a t

val to_list : 'a t -> 'a list
