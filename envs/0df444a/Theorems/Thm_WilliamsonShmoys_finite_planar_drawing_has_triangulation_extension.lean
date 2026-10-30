-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_drawing_has_triangulation_extension
-- name    : WilliamsonShmoys.finite_planar_drawing_has_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:55:37.764127+00:00
-- url     : https://prove2.me/theorems/689e997a-9a79-4277-9d35-37dc5551e5d9
-- title:
--   Triangulating extension of a finite planar drawing
-- statement:
--   Any drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_drawing_has_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
