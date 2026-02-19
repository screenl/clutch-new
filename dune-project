(lang dune 3.17)
; version in current ci image

; update to rocq 0.11 with dune 3.21
(using coq 0.10)

(name clutch)

(generate_opam_files true)

(source (github logsem/clutch))

(authors "Simon Oddershede Gregersen"
         "Alejandro Aguirre"
         "Philipp G. Haselwarter"
         "Kwing Hei Li"
         "Markus de Medeiros"
         "Joseph Tassarotti"
         "Lars Birkedal")

(maintainers "Simon Oddershede Gregersen <s.gregersen@nyu.edu>")

(homepage "https://github.com/logsem/clutch")

(license MIT)

; (documentation https://url/to/documentation)

(package
 (name rocq-clutch)
 (synopsis "Higher-order probabilistic separation logics")
 (depends ocaml
  (rocq-core (and (>= "9.1") (< "9.2~")))
  rocq-stdlib
  (rocq-iris (or (= "dev.2026-02-05.0.9815f03b") (= "dev")))
  (rocq-iris-heap-lang (or (= "dev.2026-02-05.0.9815f03b") (= "dev")))
  coq-coquelicot
  coq-autosubst
  (rocq-hierarchy-builder (= "1.10.1"))
  (rocq-mathcomp-ssreflect (= "2.5.0"))
  (rocq-mathcomp-solvable (= "2.5.0"))
  (rocq-elpi (= "3.2.0"))
  (elpi (= "3.4.2")))
 (tags
  ("awesome" "separation logic" probabilities)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
