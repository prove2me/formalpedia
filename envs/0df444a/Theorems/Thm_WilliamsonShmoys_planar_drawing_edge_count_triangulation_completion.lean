-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_triangulation_completion
-- name    : WilliamsonShmoys.planar_drawing_edge_count_triangulation_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:12:27.738309+00:00
-- url     : https://prove2.me/theorems/dd58161d-93ef-48d9-859a-7e826c258221
-- title:
--   Planar drawing completion with triangulation edge count
-- statement:
--   A planar graph on at least three vertices is contained, on the same vertex type, in a planar graph with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_IsPlanarMaximalSupergraphForEdgeCountCompletion

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ X : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      (∀ u v, W.Adj u v → X.Adj u v) ∧
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by sorry
