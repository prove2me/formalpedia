-- Prove2me | solution 1 for lean_workbook_plus_82005
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:28:53.891963+00:00
-- url     : https://prove2.me/submissions/253c065f-55d2-4471-a06f-65e6fa9aca40

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : f = fun x => 4 * x * (1 - x)) :
    ∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1 := by
  subst f
  intro x hx
  change 0 ≤ 4 * x * (1 - x) ∧ 4 * x * (1 - x) ≤ 1
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) hx.1) (sub_nonneg.mpr hx.2)
  · nlinarith [sq_nonneg (2 * x - 1)]
