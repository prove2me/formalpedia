-- Prove2me | solution 1 for lean_workbook_plus_69597
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:40:17.904101+00:00
-- url     : https://prove2.me/submissions/a5aef22b-247a-434a-94e1-a5dd137e02d5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

theorem solution (k : ℕ) : Real.sqrt (k + 1) ≤ 1 + k / (Real.sqrt k + 1) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs := Real.sqrt_nonneg (k : ℝ)
  have ht := Real.sqrt_nonneg ((k : ℝ) + 1)
  have ht2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
  have hst : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have ht1 : 1 ≤ Real.sqrt ((k : ℝ) + 1) := by nlinarith
  have hd : 0 < Real.sqrt (k : ℝ) + 1 := by linarith
  apply (sub_le_iff_le_add').mp
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr ht1)]
