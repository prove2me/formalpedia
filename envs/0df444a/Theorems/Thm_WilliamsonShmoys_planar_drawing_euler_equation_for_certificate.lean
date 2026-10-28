-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_for_certificate
-- name    : WilliamsonShmoys.planar_drawing_euler_equation_for_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:17:58.39395+00:00
-- url     : https://prove2.me/theorems/ac21768b-5faf-4999-a958-ce35afa3f136
-- title:
--   Euler equation for a connected planar drawing
-- statement:
--   A connected graph with the supplied finite crossing-free drawing has a natural-number face count satisfying Euler’s equation. This isolates the topological step of obtaining a plane embedding from the drawing data and applying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_equation_for_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
