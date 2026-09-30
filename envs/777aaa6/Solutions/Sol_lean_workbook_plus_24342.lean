-- Prove2me | solution 1 for lean_workbook_plus_24342
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T16:48:24.108172+00:00
-- url     : https://prove2.me/submissions/5468226c-9170-47dc-8962-7c8a5a89fcd2

import Mathlib.Analysis.Complex.Basic

theorem solution : ¬ (∀ (p : ℕ) (hp : p.Prime) (hp_mod_4_eq_3 : p ≡ 3 [ZMOD 4]), ¬∃ (x y z : ℕ), (x ^ 4 + p * y ^ 4 = z ^ 4)) := by
  intro h
  exact h 3 Nat.prime_three (by decide) ⟨0, 0, 0, by norm_num⟩
