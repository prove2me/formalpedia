-- Prove2me | solution 1 for lean_workbook_plus_56565
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:58:58.091774+00:00
-- url     : https://prove2.me/submissions/d79971e1-6e68-4c8a-b48e-d77aa2be40bd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ∀ x : ℝ, (x >= 0 ∧ 3 * x ^ 3 - 6 * x ^ 2 + 5 * x - 12 <= 0) → x ^ 5 - 2 * x ^ 4 - 3 * x ^ 3 + 12 * x - 8 <= 0   := by
  intro x h
  obtain ⟨hx, hg⟩ := h
  have hx5 : x < 5 / 2 := by
    by_contra hn
    have h2 : 0 ≤ x - 2 := by linarith
    nlinarith [mul_nonneg h2 (sq_nonneg x)]
  have hs : x ^ 2 ≤ 25 / 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 5 / 2 - x by linarith) (show 0 ≤ 5 / 2 + x by linarith)]
  have hc : x ^ 3 - 4 * x - 8 ≤ 0 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hs)]
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x - 1)) hc
  nlinarith
