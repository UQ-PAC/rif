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
 (synopsis "Perform weak-memory-effect checks on a disassembled ARM64 binary.")
 (depends
   "ocaml"
   "dune"
   ("asli" (>= 0.3.0))
   ("aslp_client_server_ocaml" (>= 0.1.2))
   ("ocaml-protoc-plugin" (>= 6.1.0))
   ("datalog" (>= 0.7))
   "yojson"
   "base64"
   "angstrom"
   "ocamlgraph"
   "conf-llvm"
   "ctypes"
   "ctypes-foreign"
 )
 (tags (decompiler static-analysis formal-methods))
)

