-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono_of_edgeSet_subset__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
-- name    : WilliamsonShmoys.edge_count_mono_of_edgeSet_subset__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:24:47.093362+00:00
-- url     : https://prove2.me/theorems/5f617f58-bc0c-4a61-993f-2dbbd654e80a
-- title:
--   Edge count monotonicity under inclusion
-- statement:
--   For finite simple graphs, inclusion of edge sets implies that the first graph has no more edges than the second.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono_of_edgeSet_subset__p2m_dbd442e1_f792_46a3_a33f_c17e2f3c96c0_a1
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hsub : H.edgeSet ⊆ K.edgeSet) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  sorry
