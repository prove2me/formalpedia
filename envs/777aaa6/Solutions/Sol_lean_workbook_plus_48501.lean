-- Prove2me | solution 1 for lean_workbook_plus_48501
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:27:13.384184+00:00
-- url     : https://prove2.me/submissions/53760d8e-aca7-4925-9e4b-2b2e4312847c

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace FourthPowerLastDigit

theorem last_digit (n : ℕ) :
    n ^ 4 % 10 = if n % 2 = 0 then (if n % 5 = 0 then 0 else 6)
      else (if n % 5 = 0 then 5 else 1) := by
  have hr : n % 10 < 10 := Nat.mod_lt _ (by decide)
  have h2 : n % 2 = (n % 10) % 2 := by omega
  have h5 : n % 5 = (n % 10) % 5 := by omega
  interval_cases h : n % 10 <;> norm_num [Nat.pow_mod, h, h2, h5]

theorem corrected_iff (n : ℕ) : n ^ 4 % 10 = 1 ↔ n % 2 = 1 ∧ ¬ 5 ∣ n := by
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2 <;>
    by_cases h5 : n % 5 = 0 <;>
      simp [last_digit, h2, h5, Nat.dvd_iff_mod_eq_zero]

theorem possible_digits (r : ℕ) :
    (∃ n : ℕ, n ^ 4 % 10 = r) ↔ r = 0 ∨ r = 1 ∨ r = 5 ∨ r = 6 := by
  constructor
  · rintro ⟨n, rfl⟩
    rw [last_digit]
    split_ifs <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨5, by norm_num⟩
    · exact ⟨2, by norm_num⟩

theorem counterfamily (k : ℕ) :
    0 < 10 * k + 5 ∧ (10 * k + 5) % 2 = 1 ∧ (10 * k + 5) ^ 4 % 10 = 5 := by
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

theorem unbounded_counterexamples (N : ℕ) :
    ∃ n : ℕ, N < n ∧ n % 2 = 1 ∧ n ^ 4 % 10 = 5 := by
  exact ⟨10 * N + 5, by omega, (counterfamily N).2⟩

end FourthPowerLastDigit

theorem solution : ¬ (∀ n : ℕ, n % 2 = 1 → n ^ 4 % 10 = 1) := by
  intro h
  have hbad := h 5 (by norm_num)
  norm_num at hbad
