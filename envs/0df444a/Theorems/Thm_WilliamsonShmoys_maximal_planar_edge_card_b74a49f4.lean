-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_card_b74a49f4
-- name    : WilliamsonShmoys.maximal_planar_edge_card_b74a49f4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:49:48.65308+00:00
-- url     : https://prove2.me/theorems/e6995042-8f32-4fbb-86cf-709b208a9557
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An inclusion-maximal graph with the stated planar drawing and at least three vertices has exactly `3n − 6` edges. The proof must show that maximality forces a triangulation, including the connectedness and small-face cases, then derive the count from Euler's formula. At `n = 3`, maximality gives the triangle and the equation holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_card_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
