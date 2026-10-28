-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_bound_7f31c9a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_edge_bound_7f31c9a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:16:50.385284+00:00
-- url     : https://prove2.me/theorems/7c7c4790-5dac-489e-85e5-b201ad65f4ff
-- title:
--   Same-vertex triangulation and edge count for a finite planar drawing
-- statement:
--   Every finite simple graph on at least three vertices with the given crossing-free drawing can be extended, on the same vertex type, to a drawable simple graph whose edge count attains the planar triangulation count; the original graph’s edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_edge_bound_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ u v, K.Adj u v → H.Adj u v) ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
