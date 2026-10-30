-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_96423339_d6c7_499e_a706_076681b42078
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_96423339_d6c7_499e_a706_076681b42078
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:33:06.520715+00:00
-- url     : https://prove2.me/theorems/8c5f6044-b34f-4ed9-938f-ede5d931eef6
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3n − 6 edges. The proof proceeds by showing maximality forces a triangulated embedding, applying Euler’s formula, and counting each triangular face along its boundary. The size condition excludes small vertex sets where the formula does not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_96423339_d6c7_499e_a706_076681b42078
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ (M : SimpleGraph V), L ≤ M → HasPlanarDrawingOn M → M = L) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
