-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_eq_of_mutually_le
-- name    : WilliamsonShmoys.edge_count_eq_of_mutually_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:47:49.469102+00:00
-- url     : https://prove2.me/theorems/02519e67-9032-45d3-bd75-7142d6bb8745
-- title:
--   Mutual graph inclusion preserves edge count
-- statement:
--   If each of two finite simple graphs on the same vertex type is a subgraph of the other, their edge counts agree.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_eq_of_mutually_le
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V)
    (hKL : K ≤ L)
    (hLK : L ≤ K) :
    K.edgeSet.ncard = L.edgeSet.ncard := by sorry
