-- Prove2me | solution 1 for lean_workbook_plus_46273
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:13:36.185704+00:00
-- url     : https://prove2.me/submissions/1a1ce095-6118-4595-90ae-2fe79cca3dab

import Mathlib
set_option autoImplicit false

theorem solution (x y z t : ℝ) : (x^2 + x * y + y^2) * (z^2 + z * t + t^2) ≥ ((x + y / 2)^2 + 3 * y^2 / 4) * ((t + z / 2)^2 + 3 * z^2 / 4) ∧ ((x + y / 2)^2 + 3 * y^2 / 4) * ((t + z / 2)^2 + 3 * z^2 / 4) ≥ ((x + y / 2) * (t + z / 2) + 3 * y * z / 4)^2   := by
  constructor
  · apply le_of_eq
    ring
  · nlinarith only [sq_nonneg (x * z - y * t)]

#print axioms solution
