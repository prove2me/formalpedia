-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:23:24.027798+00:00
-- url     : https://prove2.me/theorems/44d3f95a-e4af-4a94-b096-ba30239a3f07
-- title:
--   Planar edge count upper bound for this target
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
