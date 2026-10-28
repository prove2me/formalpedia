-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_triangulation
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_for_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:42:10.476333+00:00
-- url     : https://prove2.me/theorems/e0ba5d4e-e2d8-4da4-a9bb-b103b70f3cfe
-- title:
--   Edge count of a maximal planar drawing for triangulation
-- statement:
--   A maximal simple graph admitting the given crossing-free drawing, with at least three vertices, has exactly 3|V|−6 edges. This discharges the planar-topology core by deriving triangulation and applying Euler’s formula; the case of exactly three vertices is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_for_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R →
      Q.edgeSet ⊆ R.edgeSet → R.edgeSet ⊆ Q.edgeSet) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
