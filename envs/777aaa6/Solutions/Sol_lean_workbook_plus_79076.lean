-- Prove2me | solution 1 for lean_workbook_plus_79076
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:53.679487+00:00
-- url     : https://prove2.me/submissions/6b956c65-2f72-47d4-a337-eede1f633eb7

import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem odd_square_quotient_even_iff (x : ℤ) (hx : x ^ 2 ≡ 1 [ZMOD 8]) :
    Even ((x ^ 2 - 1) / 8) ↔ x % 8 = 1 ∨ x % 8 = 7 := by
  change x ^ 2 % 8 = 1 at hx
  have hnonneg := Int.emod_nonneg x (by norm_num : (16 : ℤ) ≠ 0)
  have hlt := Int.emod_lt_of_pos x (by norm_num : (0 : ℤ) < 16)
  have hsquare : x ^ 2 % 16 = (x % 16) ^ 2 % 16 := by
    simpa only [pow_two] using Int.mul_emod x x 16
  rw [Int.even_iff]
  interval_cases h : x % 16 <;> norm_num [h] at hsquare <;> omega

theorem odd_square_quotient_counterfamily (k : ℕ) :
    (16 * (k : ℤ) + 3) ^ 2 ≡ 1 [ZMOD 8] ∧
      ¬ Even (((16 * (k : ℤ) + 3) ^ 2 - 1) / 8) := by
  have hmod : (16 * (k : ℤ) + 3) ^ 2 ≡ 1 [ZMOD 8] := by
    change (16 * (k : ℤ) + 3) ^ 2 % 8 = 1
    norm_num [pow_two, Int.add_emod, Int.mul_emod]
  refine ⟨hmod, ?_⟩
  rw [odd_square_quotient_even_iff _ hmod]
  norm_num [Int.add_emod, Int.mul_emod]

theorem odd_square_quotient_counterfamily_value (k : ℕ) :
    ((16 * (k : ℤ) + 3) ^ 2 - 1) / 8 = 32 * (k : ℤ) ^ 2 + 12 * k + 1 := by
  have hpoly : (16 * (k : ℤ) + 3) ^ 2 - 1 =
      (32 * (k : ℤ) ^ 2 + 12 * k + 1) * 8 := by ring
  rw [hpoly]
  omega

theorem solution : ¬ (∀ x : ℤ, x ^ 2 ≡ 1 [ZMOD 8] →
    Even ((x ^ 2 - 1) / 8)) := by
  intro h
  have hcounter := odd_square_quotient_counterfamily 0
  exact hcounter.2 (h _ hcounter.1)
