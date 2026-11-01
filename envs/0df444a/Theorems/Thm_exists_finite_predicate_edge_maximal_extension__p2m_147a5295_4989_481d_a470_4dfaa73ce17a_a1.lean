-- Prove2me | Theorems.Thm_exists_finite_predicate_edge_maximal_extension__p2m_147a5295_4989_481d_a470_4dfaa73ce17a_a1
-- name    : exists_finite_predicate_edge_maximal_extension__p2m_147a5295_4989_481d_a470_4dfaa73ce17a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:52.03519+00:00
-- url     : https://prove2.me/theorems/31f69616-0d02-4113-b177-3a374d3ef428
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any predicate on simple graphs over a fixed finite linearly ordered vertex type, a graph satisfying the predicate has an extension satisfying it that is maximal by edge-set inclusion. Explicit decidable adjacency relations are supplied wherever edgeFinset is used.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem exists_finite_predicate_edge_maximal_extension__p2m_147a5295_4989_481d_a470_4dfaa73ce17a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (N : SimpleGraph V)
    (dN : DecidableRel N.Adj) (hN : P N) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      P K ∧
      N.edgeFinset ⊆ K.edgeFinset ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        P L →
        K.edgeFinset ⊆ L.edgeFinset →
        L.edgeFinset ⊆ K.edgeFinset := by
  sorry
