-- Prove2me | Theorems.Thm_BookSixth_coloring_large_independent_set
-- name    : BookSixth.coloring_large_independent_set
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-15T21:14:10.264812+00:00
-- url     : https://prove2.me/theorems/9876d0bd-6dab-4b21-99fb-da31c6fe57ef
-- title:
--   A proper coloring has a large independent color class
-- statement:
--   Pigeonhole principle for graph colorings. If the vertices of a finite graph are properly colored with $k$ colors, some color class is independent and has at least $N/k$ vertices: there is an independent set $S$ with $N \le k|S|$. The empty coloring forces the graph empty. This is the counting step behind every chromatic-number lower bound from the probabilistic method. **Formalization Note** Lean states independence as a pairwise relation on the coercion of the set and the size bound with natural-number multiplication.
-- source:
--   Standard counting lemma for the probabilistic-method chromatic-number argument, Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, Theorem 3 setting, https://doi.org/10.1007/978-3-662-57265-8_45

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

set_option autoImplicit false

theorem BookSixth.coloring_large_independent_set (N k : Nat)
    (G : SimpleGraph (Fin N)) (c : Fin N -> Fin k)
    (hproper : forall u v, G.Adj u v -> c u != c v) :
    exists S : Finset (Fin N),
      Set.Pairwise (S : Set (Fin N)) (fun u v => Not (G.Adj u v)) /\
      Nat.le N (k * S.card) := by sorry
