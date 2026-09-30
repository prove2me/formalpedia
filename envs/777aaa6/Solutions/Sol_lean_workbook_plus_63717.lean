-- Prove2me | solution 1 for lean_workbook_plus_63717
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:18.277868+00:00
-- url     : https://prove2.me/submissions/3fba14da-c065-40f4-993c-cb91311e3487

import Mathlib
set_option autoImplicit false

theorem solution :  ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c > 0 → b / (a + 2 * b + c) + c / (a + b + 2 * c) ≤ 2 / 3   := by
  intro a b c h
  rcases h with ⟨ha, hb, hc, hs⟩
  have hd : 0 < a + 2 * b + c := by linarith
  have he : 0 < a + b + 2 * c := by linarith
  rw [div_add_div _ _ (ne_of_gt hd) (ne_of_gt he)]
  apply (div_le_iff₀ (mul_pos hd he)).2
  nlinarith [sq_nonneg a, mul_nonneg ha hb, mul_nonneg ha hc, sq_nonneg (b - c)]

#print axioms solution
