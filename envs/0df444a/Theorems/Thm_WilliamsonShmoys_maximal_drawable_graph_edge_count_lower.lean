-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:34:56.548477+00:00
-- url     : https://prove2.me/theorems/a99d815e-b43a-4a6b-896b-1ef664efb877
-- title:
--   Lower edge bound for maximal drawable graphs
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : HasPlanarDrawingOn T)
    (hmax : ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T) :
    3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
