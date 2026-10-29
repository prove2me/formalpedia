-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_extension
-- name    : WilliamsonShmoys.planar_triangulated_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:56:02.01688+00:00
-- url     : https://prove2.me/theorems/a07fc850-027b-447d-8ccc-cce877f620ba
-- title:
--   Drawable graphs extend to a triangulation
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices having exactly 3|V|−6 edges. This isolates the geometric augmentation and triangulation step used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulated_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
