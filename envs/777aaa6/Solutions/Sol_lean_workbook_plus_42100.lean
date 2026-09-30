-- Prove2me | solution 1 for lean_workbook_plus_42100
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:22:47.101591+00:00
-- url     : https://prove2.me/submissions/a2f74e6d-7e79-412f-9b03-52ea518d3ad4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases

theorem solution (n : ℕ) (hn : 0 < n) : n^5 ≡ n [ZMOD 10] := by
  have h1 : (n : ℤ) % 10 ≡ (n : ℤ) [ZMOD 10] := Int.mod_modEq _ _
  have h2 : ((n : ℤ) % 10) ^ 5 ≡ (n : ℤ) ^ 5 [ZMOD 10] := h1.pow 5
  refine h2.symm.trans (Int.ModEq.trans ?_ h1)
  have h0 : 0 ≤ (n : ℤ) % 10 := Int.emod_nonneg _ (by norm_num)
  have h10 : (n : ℤ) % 10 < 10 := Int.emod_lt_of_pos _ (by norm_num)
  generalize (n : ℤ) % 10 = r at h0 h10 ⊢
  interval_cases r <;> decide
