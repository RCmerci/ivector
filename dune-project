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
 (name rrbvec)
 (synopsis "RRB vector implementation")
 (description "Persistent RRB vector implementation for native, js_of_ocaml, and Melange.")
 (depends
  ocaml
  js_of_ocaml
  melange
  (alcotest :with-test)
  (batteries :with-test)
  (bechamel :with-test)
  (qcheck :with-test)
  (qcheck-alcotest :with-test))
 (tags
  (rrb vector persistent native js_of_ocaml melange)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
