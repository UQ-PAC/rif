(lang dune 3.17)

(name rif)

(generate_opam_files true)

(source
 (github UQ-PAC/rif))

(authors "Andrew Brown")

(maintainers "UQ-PAC")

(license BSD-3-Clause)

(package
 (name rif)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
   ocaml
   (asli (>= 0.3.0))
   (ocaml-protoc-plugin (>= 6.1.0))
   (datalog (>= 0.7))
   yojson
 )
 (tags ("add topics" "to describe" your project))
)

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
