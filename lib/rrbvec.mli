type 'a t

val empty : 'a t

val length : 'a t -> int

val is_empty : 'a t -> bool

val get : 'a t -> int -> 'a

val set : 'a t -> int -> 'a -> 'a t

val push_back : 'a t -> 'a -> 'a t

val push_front : 'a t -> 'a -> 'a t

val pop_back : 'a t -> ('a * 'a t)

val pop_front : 'a t -> ('a * 'a t)

val peek_front : 'a t -> 'a

val peek_back : 'a t -> 'a

val append : 'a t -> 'a t -> 'a t

val prepend : 'a t -> 'a t -> 'a t

val append_list : 'a t -> 'a list -> 'a t

val prepend_list : 'a t -> 'a list -> 'a t

val append_array : 'a t -> 'a array -> 'a t

val prepend_arrat : 'a t -> 'a array -> 'a t

val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc

val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc

val map : ('a -> 'b) -> 'a t -> 'b t

val subvec : 'a t -> int -> int -> 'a t

val concat : 'a t -> 'a t -> 'a t

val of_list : 'a list -> 'a t

val to_list : 'a t -> 'a list

val of_array : 'a array -> 'a t

val to_array : 'a t -> 'a array

val of_seq : 'a Seq.t -> 'a t

val to_seq : 'a t -> 'a Seq.t

(** Check internal structural invariants. Intended for tests and benchmarks.
    Raises [Failure] with the failing node/vector path when an invariant fails. *)
val invariants : 'a t -> unit
