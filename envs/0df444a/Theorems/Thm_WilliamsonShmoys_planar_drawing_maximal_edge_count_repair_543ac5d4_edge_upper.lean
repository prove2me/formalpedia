-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_edge_count_repair_543ac5d4_edge_upper
-- name    : WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4_edge_upper
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:15:10.92369+00:00
-- url     : https://prove2.me/theorems/7121dfaf-c55c-4e42-80fa-34ab4414aa96
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   A drawable simple graph on at least three vertices has at most $3|V|-6$ edges, stated without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_edge_count_repair_543ac5d4_edge_upper
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    U.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
