-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_supergraph_of_maximum_edge_cardinality__p2m_39b66288_b9dd_430f_8b7b_434cfc203be4_a1
-- name    : WilliamsonShmoys.exists_edge_supergraph_of_maximum_edge_cardinality__p2m_39b66288_b9dd_430f_8b7b_434cfc203be4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:53.547297+00:00
-- url     : https://prove2.me/theorems/fe51c08a-279b-4044-9982-c1e903ab613f
-- title:
--   A finite property class has a maximum-cardinality supergraph
-- statement:
--   Among graphs satisfying P and containing K, there is one whose edge set has maximum cardinality. This isolates the finite selection step; the parent uses it to prove maximality by inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_supergraph_of_maximum_edge_cardinality__p2m_39b66288_b9dd_430f_8b7b_434cfc203be4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (P : SimpleGraph V → Prop)
    (hP : P K) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      P H ∧
      ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        P G →
        (letI : DecidableRel K.Adj := dK
         letI : DecidableRel G.Adj := dG
         K.edgeFinset ⊆ G.edgeFinset) →
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel H.Adj := dH
         G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
