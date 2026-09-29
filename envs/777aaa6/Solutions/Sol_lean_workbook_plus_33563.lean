-- Prove2me | solution 1 for lean_workbook_plus_33563
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:09.148932+00:00
-- url     : https://prove2.me/submissions/5cac2c82-d238-49bf-840b-123d2ad3f13e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (n : ℕ) (h : a = fun n ↦ (1 / 2) * ((1 + Real.sqrt 5) / 2)^(n) + ((1 - Real.sqrt 5) / 2)^(n)) : a n = (1 / 2) * ((1 + Real.sqrt 5) / 2)^(n) + ((1 - Real.sqrt 5) / 2)^(n) := by
  (intros; simp_all)
