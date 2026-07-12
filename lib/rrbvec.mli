type 'a t

(** The empty vector. *)
val empty : 'a t

(** Return a vector containing only [value]. *)
val singleton : 'a -> 'a t

(** Return the number of values in the vector. *)
val length : 'a t -> int

(** Return [true] when the vector has no values. *)
val is_empty : 'a t -> bool

(** Return the value at [index].

    Raises [Invalid_argument] when [index] is negative or greater than or equal
    to [length v]. *)
val nth : 'a t -> int -> 'a

(** Return the value at [index], or [None] when [index] is negative or greater
    than or equal to [length v]. *)
val nth_opt : 'a t -> int -> 'a option

(** Return a vector where [index] contains [value].

    Raises [Invalid_argument] when [index] is negative or greater than or equal
    to [length v]. *)
val set : 'a t -> int -> 'a -> 'a t

(** Return a vector with [value] added at the back.

    Raises [Invalid_argument] when the resulting length would be greater than
    or equal to [max_int]. *)
val push_back : 'a t -> 'a -> 'a t

(** Return a vector with [value] added at the front.

    Raises [Invalid_argument] when the resulting length would be greater than
    or equal to [max_int]. *)
val push_front : 'a t -> 'a -> 'a t

(** Remove and return the value at the back of the vector, along with the
    remaining vector. Returns [None] when the vector is empty. *)
val pop_back : 'a t -> ('a * 'a t) option

(** Remove and return the value at the front of the vector, along with the
    remaining vector. Returns [None] when the vector is empty. *)
val pop_front : 'a t -> ('a * 'a t) option

(** Return the value at the front of the vector.

    Raises [Invalid_argument] when the vector is empty. *)
val peek_front : 'a t -> 'a

(** Return the value at the front of the vector, or [None] when the vector is
    empty. *)
val peek_front_opt : 'a t -> 'a option

(** Return the value at the back of the vector.

    Raises [Invalid_argument] when the vector is empty. *)
val peek_back : 'a t -> 'a

(** Return the value at the back of the vector, or [None] when the vector is
    empty. *)
val peek_back_opt : 'a t -> 'a option

(** Concatenate two vectors.

    Raises [Invalid_argument] when the resulting length would be greater than
    or equal to [max_int]. *)
val append : 'a t -> 'a t -> 'a t

(** Concatenate two vectors. Alias for [append]. *)
val prepend : 'a t -> 'a t -> 'a t

(** Return [v] with all values from the list appended in order. *)
val append_list : 'a t -> 'a list -> 'a t

(** Return [v] with all values from the list prepended in order. *)
val prepend_list : 'a t -> 'a list -> 'a t

(** Return [v] with all values from the array appended in order. The input array
    is copied as needed; later mutations to the array do not affect the
    vector. *)
val append_array : 'a t -> 'a array -> 'a t

(** Return [v] with all values from the array prepended in order. The input
    array is copied as needed; later mutations to the array do not affect the
    vector. *)
val prepend_array : 'a t -> 'a array -> 'a t

(** Fold over values from front to back. *)
val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc

(** Fold over values from back to front. *)
val fold_right : ('a -> 'acc -> 'acc) -> 'a t -> 'acc -> 'acc

(** Return a vector containing [f] applied to each value. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** Return a vector containing the values that satisfy [p], preserving order. *)
val filter : ('a -> bool) -> 'a t -> 'a t

(** Return a vector containing the [Some] results of [f], preserving order. *)
val filter_map : ('a -> 'b option) -> 'a t -> 'b t

(** Map each value to a vector and concatenate the results in order. *)
val concat_map : ('a -> 'b t) -> 'a t -> 'b t

(** Return a vector containing [f] applied to matching values from two vectors.

    Raises [Invalid_argument] when the vectors have different lengths. *)
val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

(** Return a vector of pairs from two vectors.

    Raises [Invalid_argument] when the vectors have different lengths. *)
val combine : 'a t -> 'b t -> ('a * 'b) t

(** Apply [f] to matching values from two vectors from front to back.

    Raises [Invalid_argument] without calling [f] when the vectors have
    different lengths. *)
val iter2 : ('a -> 'b -> unit) -> 'a t -> 'b t -> unit

(** Fold over matching values from two vectors from front to back.

    Raises [Invalid_argument] without calling [f] when the vectors have
    different lengths. *)
val fold_left2 :
  ('acc -> 'a -> 'b -> 'acc) -> 'acc -> 'a t -> 'b t -> 'acc

(** Return [true] when [p] holds for every pair of matching values. Stops at
    the first failure.

    Raises [Invalid_argument] without calling [p] when the vectors have
    different lengths. *)
val for_all2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

(** Return [true] when [p] holds for any pair of matching values. Stops at the
    first match.

    Raises [Invalid_argument] without calling [p] when the vectors have
    different lengths. *)
val exists2 : ('a -> 'b -> bool) -> 'a t -> 'b t -> bool

(** Fold over matching values from two vectors from back to front.

    Raises [Invalid_argument] without calling [f] when the vectors have
    different lengths. *)
val fold_right2 :
  ('a -> 'b -> 'acc -> 'acc) -> 'a t -> 'b t -> 'acc -> 'acc

(** Return [true] when any value satisfies [p]. Stops at the first match. *)
val exists : ('a -> bool) -> 'a t -> bool

(** Return [true] when every value satisfies [p]. Stops at the first failure. *)
val for_all : ('a -> bool) -> 'a t -> bool

(** Return the first value that satisfies [p].

    Raises [Not_found] when no value satisfies [p]. *)
val find : ('a -> bool) -> 'a t -> 'a

(** Return the first value that satisfies [p], or [None] when no value does. *)
val find_opt : ('a -> bool) -> 'a t -> 'a option

(** Return the first [Some] result of [f], or [None] when [f] returns [None] for
    every value. *)
val find_map : ('a -> 'b option) -> 'a t -> 'b option

(** Return [true] when [value] is equal to one of the vector values. *)
val mem : 'a -> 'a t -> bool

(** [equal eq left right] is [true] when [left] and [right] have the same
    length and [eq] holds for every pair of values at the same position.

    [eq] is not called when the vectors have different lengths. *)
val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool

(** Compare two vectors lexicographically using [compare_value]. The empty
    vector is smaller than any non-empty vector.

    [compare_value] may be called even when the vectors have different
    lengths. *)
val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

(** Return the value associated with [key] in [bindings]. Keys match when
    [cmp stored_key key = 0]. If multiple bindings have matching keys, return
    the value from the leftmost binding. When [cmp] is omitted, keys are
    matched using structural equality.

    Raises [Not_found] when [key] has no binding. *)
val assoc : ?cmp:('a -> 'a -> int) -> 'a -> ('a * 'b) t -> 'b

(** Like [assoc], but return [None] when [key] has no binding. *)
val assoc_opt : ?cmp:('a -> 'a -> int) -> 'a -> ('a * 'b) t -> 'b option

(** Return [true] when [key] has a binding in [bindings]. When [cmp] is omitted,
    keys are matched using structural equality. *)
val mem_assoc : ?cmp:('a -> 'a -> int) -> 'a -> ('a * 'b) t -> bool

(** Return [bindings] without the first binding whose key matches [key], if
    any. Keys match when [cmp stored_key key = 0]. When [cmp] is omitted, keys
    are matched using structural equality. *)
val remove_assoc :
  ?cmp:('a -> 'a -> int) -> 'a -> ('a * 'b) t -> ('a * 'b) t

(** Apply [f] to each value from front to back. *)
val iter : ('a -> unit) -> 'a t -> unit

(** Apply [f] to each value and its index from front to back. *)
val iteri : (int -> 'a -> unit) -> 'a t -> unit

(** Return a vector containing [f] applied to each index and value. *)
val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t

(** Return a vector with values in reverse order. *)
val rev : 'a t -> 'a t

(** Build a vector of length [n] by applying [f] to each index from [0] to
    [n - 1].

    Raises [Invalid_argument] when [n] is negative. *)
val init : int -> (int -> 'a) -> 'a t

(** Sort values using [compare], matching [List.sort] semantics. *)
val sort : ('a -> 'a -> int) -> 'a t -> 'a t

(** Sort values and remove duplicates using [compare], matching
    [List.sort_uniq] semantics. *)
val sort_uniq : ('a -> 'a -> int) -> 'a t -> 'a t

(** Partition values by [p], preserving order in both returned vectors. *)
val partition : ('a -> bool) -> 'a t -> 'a t * 'a t

(** Return the half-open slice \[[start], [stop]) as a vector. Returns [None]
    when [start] is negative, [stop] is less than [start], or [stop] is greater
    than [length v]. *)
val subvec : 'a t -> int -> int -> 'a t option

(** Concatenate two vectors.

    Raises [Invalid_argument] when the resulting length would be greater than
    or equal to [max_int]. *)
val concat : 'a t -> 'a t -> 'a t

(** Build a vector containing the list values in order. *)
val of_list : 'a list -> 'a t

(** Return the vector values as a list in order. *)
val to_list : 'a t -> 'a list

(** Build a vector containing the sequence values in order. *)
val of_seq : 'a Seq.t -> 'a t

(** Return the vector values as a lazy sequence in order. *)
val to_seq : 'a t -> 'a Seq.t

(** Build a vector containing the array values in order. The input array is
    copied as needed; later mutations to the array do not affect the vector. *)
val of_array : 'a array -> 'a t

(** Return the vector values as a new array in order. *)
val to_array : 'a t -> 'a array

module Private : sig
  (** Check internal structural invariants and the Scala Quick logarithmic
      height bound. The temporary [effectiveNumberOfSlots + 2] rebalance-window
      rule is not a per-branch tree invariant. Intended for tests and
      benchmarks. Raises [Failure] with the failing node/vector path when an
      invariant fails. *)
  val invariants : 'a t -> unit
end
