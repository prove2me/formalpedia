-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:59:40.123999+00:00
-- url     : https://prove2.me/theorems/5fac830d-330a-4033-b92d-b2d1f0f7b487
-- title:
--   Triangulate a planar drawing on a fixed vertex set
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a planar supergraph on the same vertex set whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      N.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
