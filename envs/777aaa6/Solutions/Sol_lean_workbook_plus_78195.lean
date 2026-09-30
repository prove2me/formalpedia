-- Prove2me | solution 1 for lean_workbook_plus_78195
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T06:22:26.053854+00:00
-- url     : https://prove2.me/submissions/846dd704-2fb9-473e-8695-be5254f6f3bb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem valid_domain (a : ℝ) :
    0 ≤ (2 * a * (a - 1) ^ 2 * (2 * a + 1)) /
      (a ^ 2 + 2 * a + 3) / (3 * a ^ 2 + 2 * a + 1) ↔
      a ≤ -1 / 2 ∨ 0 ≤ a := by
  have h₁ : 0 < a ^ 2 + 2 * a + 3 := by nlinarith [sq_nonneg (a + 1)]
  have h₂ : 0 < 3 * a ^ 2 + 2 * a + 1 := by nlinarith [sq_nonneg (3 * a + 1)]
  rw [le_div_iff₀ h₂, zero_mul, le_div_iff₀ h₁, zero_mul]
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have hs : 0 < (a - 1) ^ 2 := sq_pos_of_ne_zero (by linarith)
    have hp : 0 < 2 * a + 1 := by linarith
    have ha : 2 * a < 0 := by linarith
    have := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos ha hs) hp
    linarith
  · rintro (ha | ha)
    · have hn : 2 * a * (a - 1) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
      exact mul_nonneg_of_nonpos_of_nonpos hn (by linarith)
    · positivity

theorem solution : ¬ (∀ a : ℝ,
    (2 * a * (a - 1) ^ 2 * (2 * a + 1)) /
      (a ^ 2 + 2 * a + 3) / (3 * a ^ 2 + 2 * a + 1) ≥ 0) := by
  intro h
  have hc := (valid_domain (-1 / 4)).mp (h (-1 / 4))
  norm_num at hc
