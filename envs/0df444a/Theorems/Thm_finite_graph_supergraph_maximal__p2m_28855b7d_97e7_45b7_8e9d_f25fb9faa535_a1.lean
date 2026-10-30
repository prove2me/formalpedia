-- Prove2me | Theorems.Thm_finite_graph_supergraph_maximal__p2m_28855b7d_97e7_45b7_8e9d_f25fb9faa535_a1
-- name    : finite_graph_supergraph_maximal__p2m_28855b7d_97e7_45b7_8e9d_f25fb9faa535_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T18:43:20.637881+00:00
-- url     : https://prove2.me/theorems/754a9899-755e-43c7-9ae7-e29e17e81aa7
-- title:
--   Finite maximal supergraph for any graph property
-- statement:
--   Among the simple graphs extending K and satisfying P, there is one that has no proper P-satisfying supergraph on the same finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_graph_supergraph_maximal__p2m_28855b7d_97e7_45b7_8e9d_f25fb9faa535_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      P L ∧
      ∀ M : SimpleGraph V,
        Set.Subset L.edgeSet M.edgeSet →
        P M →
        M.edgeSet = L.edgeSet := by
  sorry
