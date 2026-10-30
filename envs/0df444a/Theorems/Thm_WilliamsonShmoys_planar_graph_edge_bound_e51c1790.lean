-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_bound_e51c1790
-- name    : WilliamsonShmoys.planar_graph_edge_bound_e51c1790
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:38:44.521291+00:00
-- url     : https://prove2.me/theorems/21446003-fac0-46fd-be6f-03d17c7cc1aa
-- title:
--   Planar graph edge upper bound
-- statement:
--   Every finite simple graph with a planar drawing and at least three vertices has at most 3|V|−6 edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_bound_e51c1790
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    U.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
