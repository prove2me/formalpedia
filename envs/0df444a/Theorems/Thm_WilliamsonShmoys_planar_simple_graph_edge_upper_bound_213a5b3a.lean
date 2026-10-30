-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound_213a5b3a
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound_213a5b3a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:50:03.777091+00:00
-- url     : https://prove2.me/theorems/a12f48fc-3b86-4938-b580-6ac5c51e76fb
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. Prove this by applying Euler’s formula to a connected plane extension and counting face-boundary incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound_213a5b3a
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
