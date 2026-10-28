-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_edge_count
-- name    : WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:53:01.742285+00:00
-- url     : https://prove2.me/theorems/6fecec1c-ab42-47f9-9ba6-29ea76a39185
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   If a drawable simple graph on at least three finite vertices has no strictly larger drawable supergraph on those vertices, then its edge count is three times the number of vertices minus six. This is the Euler-formula step: maximality forces a triangulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion_fixed_vertices_e7f6fb70_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y)
    (hmax : forall Z : SimpleGraph V, Y <= Z ->
      WilliamsonShmoys.HasPlanarDrawingOn Z -> Z = Y) :
    3 * Fintype.card V = Y.edgeSet.ncard + 6 := by sorry
