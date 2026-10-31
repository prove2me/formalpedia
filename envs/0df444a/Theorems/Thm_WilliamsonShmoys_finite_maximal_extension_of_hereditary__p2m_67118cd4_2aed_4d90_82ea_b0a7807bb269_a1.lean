-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_hereditary__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
-- name    : WilliamsonShmoys.finite_maximal_extension_of_hereditary__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:52:40.253965+00:00
-- url     : https://prove2.me/theorems/5b6b96d8-4ce0-42c1-a978-4ded37473014
-- title:
--   Finite hereditary graph properties have maximal extensions
-- statement:
--   For a graph on a finite vertex type, any hereditary graph property that holds of the graph has a supergraph with the property that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_maximal_extension_of_hereditary__p2m_67118cd4_2aed_4d90_82ea_b0a7807bb269_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hP : ∀ {G H : SimpleGraph V}, H.edgeSet ⊆ G.edgeSet → P G → P H)
    (N : SimpleGraph V)
    (hN : P N) :
    ∃ M : SimpleGraph V,
      N.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ K : SimpleGraph V,
        M.edgeSet ⊆ K.edgeSet → P K → K.edgeSet = M.edgeSet := by sorry
