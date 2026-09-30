-- Prove2me | solution 1 for lean_workbook_plus_67146
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:09.600538+00:00
-- url     : https://prove2.me/submissions/f33f44f6-a6bb-4e89-b0b1-dc92fb28138b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.NormNum

theorem solution (n : ℤ) : ¬ 3 ∣ n → ¬ 3 ∣ n^2 := by
  intro hn hsq
  rw [Int.dvd_iff_emod_eq_zero] at hn hsq
  have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h <;>
    norm_num [pow_two, Int.mul_emod, h] at hsq
