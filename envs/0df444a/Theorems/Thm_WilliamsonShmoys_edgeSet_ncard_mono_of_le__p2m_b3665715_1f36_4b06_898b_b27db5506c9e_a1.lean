-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_of_le__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_of_le__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:12:53.286998+00:00
-- url     : https://prove2.me/theorems/44863f15-85bc-4f7f-831e-29dd354c96f0
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge-set cardinality is no larger. This separates the elementary finite-set counting step from the planar completion argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_mono_of_le__p2m_b3665715_1f36_4b06_898b_b27db5506c9e_a1
    {V : Type} [Fintype V]
    {K G : SimpleGraph V}
    (hKG : K ≤ G) :
    K.edgeSet.ncard ≤ G.edgeSet.ncard := by sorry
