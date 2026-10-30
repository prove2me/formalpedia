-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_property__p2m_29782dd3_0f1b_4e01_b9eb_fb2f369524d3_a2
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_29782dd3_0f1b_4e01_b9eb_fb2f369524d3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:14:56.960197+00:00
-- url     : https://prove2.me/theorems/99fd24e7-a383-49b6-98ca-f4659456fe07
-- title:
--   Finite maximal supergraph for a property
-- statement:
--   For any property Q on simple graphs over a finite linearly ordered vertex type, if M satisfies Q, then there is a Q-satisfying supergraph of M whose edge count is at least that of every Q-satisfying supergraph of M.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_for_property__p2m_29782dd3_0f1b_4e01_b9eb_fb2f369524d3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (Q : SimpleGraph V → Prop) (hM : Q M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ Q N ∧
      (∀ K : SimpleGraph V, M ≤ K → Q K →
        K.edgeSet.ncard ≤ N.edgeSet.ncard) := by sorry
