-- Prove2me | solution 1 for lean_workbook_plus_77380
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T21:23:09.845622+00:00
-- url     : https://prove2.me/submissions/d4a95ca7-e614-4a0a-a445-32909046e4cc

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ x y z : ℝ, 9 * (x ^ 2 * (x ^ 2 + y ^ 2) * (x ^ 2 + z ^ 2) + y ^ 2 * (y ^ 2 + z ^ 2) * (y ^ 2 + x ^ 2) + z ^ 2 * (z ^ 2 + x ^ 2) * (z ^ 2 + y ^ 2)) + 18 * (x * y * (x ^ 2 + y ^ 2) * Real.sqrt ((x ^ 2 + z ^ 2) * (y ^ 2 + z ^ 2)) + x * z * (x ^ 2 + z ^ 2) * Real.sqrt ((x ^ 2 + y ^ 2) * (z ^ 2 + y ^ 2)) + y * z * (y ^ 2 + z ^ 2) * Real.sqrt ((y ^ 2 + x ^ 2) * (z ^ 2 + x ^ 2))) ≥ 4 * (x + y + z) ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 2) := by
  -- Counterexample (x, y, z) = (49, 49, -71): both square roots are of perfect squares
  -- (7442^2 and 5978^2), and the left side minus the right side equals -252798703488 < 0.
  intro h
  have key := h 49 49 (-71)
  have s1 : Real.sqrt (((49:ℝ) ^ 2 + (-71) ^ 2) * ((49:ℝ) ^ 2 + (-71) ^ 2)) = 7442 := by
    rw [show ((49:ℝ) ^ 2 + (-71) ^ 2) * ((49:ℝ) ^ 2 + (-71) ^ 2) = (7442:ℝ) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have s2 : Real.sqrt (((49:ℝ) ^ 2 + 49 ^ 2) * ((-71) ^ 2 + 49 ^ 2)) = 5978 := by
    rw [show ((49:ℝ) ^ 2 + 49 ^ 2) * ((-71) ^ 2 + 49 ^ 2) = (5978:ℝ) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [s1, s2] at key
  linarith
