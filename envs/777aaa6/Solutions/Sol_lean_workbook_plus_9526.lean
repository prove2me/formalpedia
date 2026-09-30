-- Prove2me | solution 1 for lean_workbook_plus_9526
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:46:48.303637+00:00
-- url     : https://prove2.me/submissions/898802ac-646f-4665-be34-846a1070b326

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace MersennePowerOfThree

theorem three_pow_mod_eight (q : ℕ) : 3 ^ q % 8 = 1 ∨ 3 ^ q % 8 = 3 := by
  induction q with
  | zero => norm_num
  | succ q ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h <;> norm_num [h]

theorem no_large_exponent (n q : ℕ) (hn : 3 ≤ n) : 2 ^ n - 1 ≠ 3 ^ q := by
  intro heq
  have hdiv : 8 ∣ 2 ^ n := by
    simpa using pow_dvd_pow (2 : ℕ) hn
  have hmod : 2 ^ n % 8 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hpos : 0 < (2 : ℕ) ^ n := pow_pos (by decide) n
  have hadd : 3 ^ q + 1 = 2 ^ n := by omega
  have hm : (3 ^ q + 1) % 8 = 0 := by rw [hadd, hmod]
  rw [Nat.add_mod] at hm
  rcases three_pow_mod_eight q with h | h <;> norm_num [h] at hm

theorem classification (n q : ℕ) :
    2 ^ n - 1 = 3 ^ q ↔ (n = 1 ∧ q = 0) ∨ (n = 2 ∧ q = 1) := by
  constructor
  · intro heq
    have hn : n ≤ 2 := by
      by_contra h
      exact no_large_exponent n q (by omega) heq
    obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    · change 0 = 3 ^ q at heq
      have hpos : 0 < (3 : ℕ) ^ q := pow_pos (by decide) q
      omega
    · have hq : q = 0 := (Nat.pow_right_inj (by decide : 1 < (3 : ℕ))).mp
        (show (3 : ℕ) ^ q = 3 ^ 0 by simpa using heq.symm)
      exact Or.inl ⟨rfl, hq⟩
    · have hq : q = 1 := (Nat.pow_right_inj (by decide : 1 < (3 : ℕ))).mp
        (show (3 : ℕ) ^ q = 3 ^ 1 by simpa using heq.symm)
      exact Or.inr ⟨rfl, hq⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

end MersennePowerOfThree

theorem solution (n q : ℕ) (h₀ : 2 < n) (_h₁ : 0 < q)
    (h₂ : 2 ^ n - 1 = 3 ^ q) : False := by
  exact MersennePowerOfThree.no_large_exponent n q (by omega) h₂
