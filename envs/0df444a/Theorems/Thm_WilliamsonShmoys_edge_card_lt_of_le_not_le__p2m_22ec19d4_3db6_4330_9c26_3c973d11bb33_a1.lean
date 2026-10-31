-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_lt_of_le_not_le__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
-- name    : WilliamsonShmoys.edge_card_lt_of_le_not_le__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:32:27.206406+00:00
-- url     : https://prove2.me/theorems/e1ff03c8-e02b-4b3d-8c03-9044150b63ed
-- title:
--   Proper graph inclusion increases finite edge count
-- statement:
--   For finite simple graphs, if L is a subgraph of H and H is not a subgraph of L, then L has strictly fewer edges. This follows by viewing edgeFinset L as a proper subset of edgeFinset H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_card_lt_of_le_not_le__p2m_22ec19d4_3db6_4330_9c26_3c973d11bb33_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L H : SimpleGraph V) [DecidableRel L.Adj] [DecidableRel H.Adj]
    (hLH : L ≤ H) (hnot : ¬ H ≤ L) :
    L.edgeFinset.card < H.edgeFinset.card := by sorry
