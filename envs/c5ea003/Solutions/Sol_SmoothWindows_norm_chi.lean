-- Prove2me | solution 1 for SmoothWindows.norm_chi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:29:00.65135+00:00
-- url     : https://prove2.me/submissions/1c1deba0-ac24-47df-936a-2311cf151f51

import Mathlib
import Definitions.Def_Algebra_SmoothWindows_GaborOperators

open SmoothWindows Complex

theorem solution (x : ℝ) : ‖chi x‖ = 1 := by
  simpa [chi] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
