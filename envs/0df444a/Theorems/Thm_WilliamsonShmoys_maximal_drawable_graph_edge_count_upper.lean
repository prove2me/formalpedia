-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_upper
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:30:30.33368+00:00
-- url     : https://prove2.me/theorems/d0b1c706-7e32-47d9-9676-1be186e8c54d
-- title:
--   Upper edge bound for drawable simple graphs
-- statement:
--   A drawable simple graph with at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_upper
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
