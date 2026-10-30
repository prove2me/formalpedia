-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph
-- name    : WilliamsonShmoys.exists_triangulated_drawable_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:50:04.854931+00:00
-- url     : https://prove2.me/theorems/3d83e52d-d7f3-4064-9901-f4d565126921
-- title:
--   Drawable graph completion to a triangulation
-- statement:
--   Every drawable simple graph on a fixed finite ordered vertex set with at least three vertices is contained in a drawable supergraph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_drawable_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W ≤ X ∧
      WilliamsonShmoys.HasPlanarDrawingOn X ∧
      3 * Fintype.card V = X.edgeSet.ncard + 6 := by
  sorry
