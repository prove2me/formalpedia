-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_7c5eea9e
-- name    : WilliamsonShmoys.planar_drawing_euler_formula_7c5eea9e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:48:20.189442+00:00
-- url     : https://prove2.me/theorems/0eb86e9b-e28f-4551-bd2b-6d332c44b169
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected finite graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_formula_7c5eea9e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 := by sorry
