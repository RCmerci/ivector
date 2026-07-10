# rrbvec

`rrbvec` is a persistent RRB vector implementation for OCaml. It supports
native OCaml, `js_of_ocaml`, and Melange, and provides efficient indexed access,
updates, appends, and concatenation while preserving previous versions.

## Example

```ocaml
let vector = Rrbvec.of_list [ 1; 2; 3 ]
let updated = Rrbvec.set vector 1 10

let () =
  assert (Rrbvec.to_list vector = [ 1; 2; 3 ]);
  assert (Rrbvec.to_list updated = [ 1; 10; 3 ])
```

## Time complexity

Let `n` be the vector length and `m` the length of a second vector or input
collection. RRB trees use a branching factor of 32, so logarithmic operations
have a very shallow `log32` path.

| API | Time complexity | Notes |
| --- | --- | --- |
| `length`, `is_empty` | `O(1)` | Stored in the vector header. |
| `nth`, `nth_opt` | `O(log32 n)` worst case | `O(1)` when the value is in an edge buffer. |
| `set` | `O(log32 n)` worst case | Copies only the path to the changed value. |
| `push_front`, `push_back` | `O(log32 n)` worst case | `O(1)` while the corresponding edge buffer has room. |
| `pop_front`, `pop_back` | `O(log32 n)` worst case | `O(1)` when no tree refill is required. |
| `peek_front`, `peek_back` | `O(log32 n)` worst case | `O(1)` when the value is in an edge buffer. |
| `append`, `prepend`, `concat` | `O(log32 (n + m))` worst case | Shares unchanged tree structure. |
| `subvec` | `O(log32 n)` | Shares complete internal subtrees. |
| `of_list`, `of_array`, `to_list`, `to_array` | `O(n)` | Converts every value once. |
| `map`, `fold_left`, `fold_right`, `iter` | `O(n)` | Visits every value once. |
| `sort`, `sort_uniq` | `O(n log n)` | Uses OCaml list sorting internally. |

## Development

Build the project and run the test suite with Dune:

```sh
dune build
dune runtest
```

Run the native benchmark with:

```sh
dune exec bin/benchmark.exe
```
