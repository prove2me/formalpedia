-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_predicate__p2m_d0a96286_d6d0_4f9d_8f16_8ff04549e9c7_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d0a96286_d6d0_4f9d_8f16_8ff04549e9c7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:33.640535+00:00
-- url     : https://prove2.me/theorems/9396be62-1e50-4a6f-b441-03ad928f83c3
-- title:
--   Finite maximal supergraph for a graph predicate
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate is contained in a predicate-satisfying graph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_predicate__p2m_d0a96286_d6d0_4f9d_8f16_8ff04549e9c7_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      P K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet →
        P L →
        L.edgeSet ⊆ K.edgeSet := by sorry
