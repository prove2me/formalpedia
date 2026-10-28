-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_completion_edge_count_same_vertices
-- name    : WilliamsonShmoys.planar_drawingOn_completion_edge_count_same_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:24:55.092202+00:00
-- url     : https://prove2.me/theorems/febcb416-2238-45f5-9e25-7dd1dce07c3e
-- title:
--   Drawable supergraph completion with the planar edge count
-- statement:
--   Any drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_completion_edge_count_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z) :
    ∃ T : SimpleGraph V, Z ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
