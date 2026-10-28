-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edges_4f89c2
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:47:31.867793+00:00
-- url     : https://prove2.me/theorems/2fe69c8f-544b-45ba-9fa5-3da2d070e307
-- title:
--   Exact edge count of a maximal planar drawing
-- statement:
--   A simple graph on at least three vertices that is maximal among planar graphs on those vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ S : SimpleGraph V, R.edgeSet ⊂ S.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn S) :
    R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
