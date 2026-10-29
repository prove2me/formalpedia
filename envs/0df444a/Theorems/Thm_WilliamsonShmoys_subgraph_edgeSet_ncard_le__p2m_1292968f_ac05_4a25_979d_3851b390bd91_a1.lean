-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edgeSet_ncard_le__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- name    : WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:42:42.063326+00:00
-- url     : https://prove2.me/theorems/51bde848-4507-4eff-90cb-3722c6b911c2
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of adjacency relations implies inclusion of edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.subgraph_edgeSet_ncard_le__p2m_1292968f_ac05_4a25_979d_3851b390bd91_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
