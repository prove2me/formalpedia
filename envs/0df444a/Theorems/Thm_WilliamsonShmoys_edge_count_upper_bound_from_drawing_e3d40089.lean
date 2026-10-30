-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_upper_bound_from_drawing_e3d40089
-- name    : WilliamsonShmoys.edge_count_upper_bound_from_drawing_e3d40089
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:11:32.617992+00:00
-- url     : https://prove2.me/theorems/820dd98c-2d64-44e2-9707-893186b95c7a
-- title:
--   Planar drawing edge count upper bound
-- statement:
--   A finite simple graph with the given crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_upper_bound_from_drawing_e3d40089
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
