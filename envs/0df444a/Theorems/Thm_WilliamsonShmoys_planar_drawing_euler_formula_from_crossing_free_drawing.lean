-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_from_crossing_free_drawing
-- name    : WilliamsonShmoys.planar_drawing_euler_formula_from_crossing_free_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:27:40.132639+00:00
-- url     : https://prove2.me/theorems/5709725d-da41-4e99-bc0b-263275feb74e
-- title:
--   Euler face formula for a connected crossing-free drawing
-- statement:
--   A connected graph with the supplied crossing-free drawing has a finite number of faces satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_formula_from_crossing_free_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : G.Connected)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ F : ℕ, Fintype.card V + F = G.edgeSet.ncard + 2 := by sorry
