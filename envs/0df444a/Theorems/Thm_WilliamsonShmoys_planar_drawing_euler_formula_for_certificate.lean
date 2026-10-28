-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula_for_certificate
-- name    : WilliamsonShmoys.planar_drawing_euler_formula_for_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:30:52.393044+00:00
-- url     : https://prove2.me/theorems/14554ba3-ba70-4219-bb96-a24e8bae9efb
-- title:
--   Euler face-count formula for a connected planar drawing
-- statement:
--   A connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_formula_for_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : Nat, Fintype.card V + f = K.edgeSet.ncard + 2 := by
  sorry
