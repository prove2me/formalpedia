-- Prove2me | solution 1 for RhinViola.psi_invariant_under_tau
-- status  : ACCEPTED   (prove)
-- author  : @Winningatmath
-- created : 2026-10-16T20:36:37.513609+00:00
-- url     : https://prove2.me/submissions/fc7b6063-5855-44e1-97b3-aadc8a309a3d

import Mathlib

theorem solution
    (x y : ℂ) (hx : x ≠ 0) (hxy : 1 - x * y ≠ 0) :
    (fun u v : ℂ => u * v * (1 - u) * (1 - v) / (1 - u * v))
      ((1 - x) / (1 - x * y)) (1 - x * y) =
    (fun u v : ℂ => u * v * (1 - u) * (1 - v) / (1 - u * v)) x y := by
  grind
