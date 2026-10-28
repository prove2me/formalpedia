-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_exact_count
-- name    : WilliamsonShmoys.planar_drawing_completion_exact_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:08:57.653376+00:00
-- url     : https://prove2.me/theorems/efb0a43e-4e35-40a2-b271-6686b0ab398f
-- title:
--   Drawable graph completion with exact planar edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_completion_exact_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
