-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulation_edge_count_repair
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_repair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:02:50.061862+00:00
-- url     : https://prove2.me/theorems/6beb5ec3-4ac6-4763-86a7-72bb05ff77b5
-- title:
--   Drawable supergraph with triangulation edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertex type whose edge count is three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulation_edge_count_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
