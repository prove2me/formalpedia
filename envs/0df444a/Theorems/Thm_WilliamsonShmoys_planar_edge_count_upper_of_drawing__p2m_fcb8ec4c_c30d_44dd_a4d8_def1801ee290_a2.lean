-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:55.973435+00:00
-- url     : https://prove2.me/theorems/84c43119-f87e-4738-abb0-0796ef4e5b94
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   This isolates the standard upper bound for a finite drawable simple graph. The proof route is Euler’s formula with face-boundary counting; disconnected cases can be handled by the usual planar graph counting argument. The size hypothesis avoids small-vertex exceptions and keeps the natural-number subtraction cutoff explicit. This removes the upper-bound half of the target from the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_of_drawing__p2m_fcb8ec4c_c30d_44dd_a4d8_def1801ee290_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
