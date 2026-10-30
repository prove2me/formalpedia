-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_96423339_d6c7_499e_a706_076681b42078
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_96423339_d6c7_499e_a706_076681b42078
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:09:22.246037+00:00
-- url     : https://prove2.me/theorems/8b46f3a1-b0d7-4f9b-baa7-2c1aaf8f50ac
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices is contained, on the same vertex set, in a drawable graph with exactly 3n−6 edges. This provides the maximal planar extension whose edge count is used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_96423339_d6c7_499e_a706_076681b42078
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ HasPlanarDrawingOn L ∧
        L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
