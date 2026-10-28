-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_drawingOn_triangulation
-- name    : WilliamsonShmoys.planar_edge_bound_from_drawingOn_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T10:19:55.754248+00:00
-- url     : https://prove2.me/theorems/df5b7716-886f-4c81-a3fd-ebfa1ccd5c5b
-- title:
--   Planar edge bound from a triangulated supergraph
-- statement:
--   A finite simple graph on at least three vertices with a drawing satisfying HasPlanarDrawingOn has a planar supergraph on the same vertex type whose edge count is 3|V|−6, and the original edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_drawingOn_triangulation {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
