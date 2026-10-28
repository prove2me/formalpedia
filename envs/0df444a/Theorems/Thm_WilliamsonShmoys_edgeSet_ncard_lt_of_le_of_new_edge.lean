-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_le_of_new_edge
-- name    : WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_new_edge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:10:51.969243+00:00
-- url     : https://prove2.me/theorems/178a0abc-e43c-4f9a-b72c-99f7ef266421
-- title:
--   A newly added edge strictly increases edge count
-- statement:
--   If one finite simple graph is a subgraph of another and the latter contains an edge absent from the former, then its edge set has strictly greater cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_new_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (u v : V)
    (hnot : ¬ G.Adj u v)
    (hadj : H.Adj u v) :
    G.edgeSet.ncard < H.edgeSet.ncard := by sorry
