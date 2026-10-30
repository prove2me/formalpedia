-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound
-- name    : WilliamsonShmoys.planar_graph_edge_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:22:18.145249+00:00
-- url     : https://prove2.me/theorems/af19c0fd-e3b8-4b6f-b9a4-d0c669483b59
-- title:
--   Planar graphs have at most 3n−6 edges
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
