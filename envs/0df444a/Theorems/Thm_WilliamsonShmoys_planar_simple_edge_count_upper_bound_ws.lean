-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_count_upper_bound_ws
-- name    : WilliamsonShmoys.planar_simple_edge_count_upper_bound_ws
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:52:49.291035+00:00
-- url     : https://prove2.me/theorems/f1467d53-2060-44d4-9ba5-e870d6b46586
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   A drawable simple graph with at least three vertices has at most three times its number of vertices minus six edges, written using addition to avoid truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_count_upper_bound_ws
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
