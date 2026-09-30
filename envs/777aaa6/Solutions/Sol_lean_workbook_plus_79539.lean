-- Prove2me | solution 1 for lean_workbook_plus_79539
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:42.286991+00:00
-- url     : https://prove2.me/submissions/59b92561-e19e-4a54-bd2f-b8297aab8f2f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (n : ℕ) : ((n:ℝ)^3 - 1) / ((n:ℝ)^3 + 1) =
    (n - 1) / (n + 1) * ((n:ℝ)^2 + n + 1) / ((n:ℝ)^2 - n + 1) := by
  have hm : (n : ℝ)^3 - 1 = (n - 1) * ((n : ℝ)^2 + n + 1) := by ring
  have hp : (n : ℝ)^3 + 1 = (n + 1) * ((n : ℝ)^2 - n + 1) := by ring
  rw [hm, hp]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
