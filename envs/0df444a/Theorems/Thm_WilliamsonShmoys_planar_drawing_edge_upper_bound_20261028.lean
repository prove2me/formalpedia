-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_20261028
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T02:12:38.1569+00:00
-- url     : https://prove2.me/theorems/6e0d9b1f-ef90-4252-a1c7-5ef9b80d7d95
-- title:
--   Planar drawings satisfy the simple-graph edge upper bound
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most \(3|V|-6\) edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
