-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_of_finite__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:41:14.665016+00:00
-- url     : https://prove2.me/theorems/58404e00-c31f-4c1b-aead-ffbc7e09c12f
-- title:
--   Maximal extension for a hereditary predicate on finite graphs
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type that is preserved when passing to subgraphs, every graph satisfying the predicate has a predicate-satisfying supergraph maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_extension_of_finite__p2m_5269810a_aaa3_482e_ac1c_32cbc68ffb91_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hhered : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (G : SimpleGraph V) (hG : P G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by sorry
