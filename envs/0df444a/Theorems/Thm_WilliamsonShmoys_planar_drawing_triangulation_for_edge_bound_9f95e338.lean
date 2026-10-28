-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_for_edge_bound_9f95e338
-- name    : WilliamsonShmoys.planar_drawing_triangulation_for_edge_bound_9f95e338
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:56:55.330451+00:00
-- url     : https://prove2.me/theorems/3f5a0f00-9091-433c-b28d-bf140c507cf3
-- title:
--   Triangulate a finite planar graph on the same vertices
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices is contained in a planar graph on the same vertex type having exactly 3|V| − 6 edges. The hypotheses retain the vertex lower bound needed for the maximal planar edge formula. An independent proof route is to use the finite planar graph augmentation theorem to extend H to a maximal planar supergraph without adding vertices, then apply Euler’s formula and count face-edge incidences. This removes the geometric and Euler-counting argument from the parent; that augmentation argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_for_edge_bound_9f95e338
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, H ≤ T ∧ HasPlanarDrawingOn T ∧
      T.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
