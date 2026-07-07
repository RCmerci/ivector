(lang dune 3.23)
(using melange 1.0)

(name rrbvec)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(package
 (name rrbvec-core)
 (synopsis "RRB vector core implementation")
 (description "Platform-independent RRB vector implementation.")
 (depends ocaml)
 (tags
  (rrb vector persistent)))

(package
 (name rrbvec-native)
 (synopsis "Native implementation package for rrbvec")
 (description "Native implementation package for rrbvec-core.")
 (depends
  ocaml
  rrbvec-core
  (alcotest :with-test)
  (batteries :with-test)
  (bechamel :with-test)
  (qcheck :with-test)
  (qcheck-alcotest :with-test))
 (tags
  (rrb vector persistent native)))

(package
 (name rrbvec-jsoo)
 (synopsis "js_of_ocaml implementation package for rrbvec")
 (description "js_of_ocaml implementation package for rrbvec-core.")
 (depends
  ocaml
  rrbvec-core
  js_of_ocaml)
 (tags
  (rrb vector persistent js_of_ocaml)))

(package
 (name rrbvec-melange)
 (synopsis "Melange implementation package for rrbvec")
 (description "Melange implementation package for rrbvec-core.")
 (depends
  ocaml
  rrbvec-core
  melange)
 (tags
  (rrb vector persistent melange)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
