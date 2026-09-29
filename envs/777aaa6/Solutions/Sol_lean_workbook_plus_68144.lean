-- Prove2me | solution 1 for lean_workbook_plus_68144
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:07.779772+00:00
-- url     : https://prove2.me/submissions/3c514f73-eff9-418b-b306-754850237a2b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ) (h₁ : x = 2 * t ^ 2 - t - 1) (h₂ : y = 2 * t ^ 2 + t - 1) (h₃ : z = t) : z = t := by
  (intros; simp_all)
