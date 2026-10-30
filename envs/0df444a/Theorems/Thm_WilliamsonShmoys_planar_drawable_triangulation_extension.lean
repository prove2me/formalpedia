-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_triangulation_extension
-- name    : WilliamsonShmoys.planar_drawable_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:00:44.168902+00:00
-- url     : https://prove2.me/theorems/510e0039-cd94-40e2-94b3-d7488deb89be
-- title:
--   Triangulation extension of a drawable graph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type whose edge count is exactly the planar triangulation bound. This includes disconnected graphs and the three-vertex case. The assertion packages the main augmentation theorem and its exact edge count; the parent uses the edge count to show the extension is proper under strict sparsity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
        WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry
