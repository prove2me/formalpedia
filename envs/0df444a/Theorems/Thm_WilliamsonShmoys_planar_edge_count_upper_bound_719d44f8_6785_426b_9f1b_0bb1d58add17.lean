-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_719d44f8_6785_426b_9f1b_0bb1d58add17
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_719d44f8_6785_426b_9f1b_0bb1d58add17
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:21:45.26859+00:00
-- url     : https://prove2.me/theorems/46e934fc-bcb1-4838-ab42-58c452c0a996
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   Every finite simple graph with a drawing as defined by HasPlanarDrawingOn and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound_719d44f8_6785_426b_9f1b_0bb1d58add17
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    P.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
