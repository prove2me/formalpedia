-- Prove2me | solution 1 for lean_workbook_plus_64842
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:26:14.208221+00:00
-- url     : https://prove2.me/submissions/b84cbcf6-73c7-4946-8485-665f08dd111b

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

private theorem asc_factorial_congruence {M a b : ℕ} (h : Nat.ModEq M a b) (k : ℕ) :
    Nat.ModEq M (a.ascFactorial k) (b.ascFactorial k) := by
  induction k with
  | zero => simp only [Nat.ascFactorial_zero]; exact Nat.ModEq.refl 1
  | succ k ih =>
    rw [Nat.ascFactorial_succ, Nat.ascFactorial_succ]
    exact (h.add_right k).mul ih

private theorem binomial_congruence (k m : ℕ) :
    Nat.ModEq m (Nat.choose (k.factorial * m + k) k) 1 := by
  have hb : Nat.ModEq (k.factorial * m) (k.factorial * m + 1) (0 + 1) :=
    (Nat.modEq_zero_iff_dvd.mpr (dvd_refl (k.factorial * m))).add_right 1
  have hp := asc_factorial_congruence hb k
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at hp
  apply Nat.ModEq.mul_left_cancel' (Nat.factorial_ne_zero k)
  simpa only [zero_add, Nat.one_ascFactorial, mul_one] using hp

private theorem strictly_larger_coprime_binomial (k m : ℕ) (hm : 0 < m) :
    ∃ n, k < n ∧ Nat.Coprime m (Nat.choose n k) := by
  refine ⟨k.factorial * m + k, ?_, ?_⟩
  · have hpos := Nat.mul_pos (Nat.factorial_pos k) hm
    omega
  · have hc := Nat.coprime_of_mul_modEq_one 1
      (show Nat.ModEq m (Nat.choose (k.factorial * m + k) k * 1) 1 by
        simpa only [mul_one] using binomial_congruence k m)
    exact hc.symm

theorem solution (k m : ℕ) (h₁ : 0 < k ∧ 0 < m) (h₂ : m ≤ k) :
    ∃ n, n ≥ k ∧ Nat.Coprime m (Nat.choose n k) := by
  obtain ⟨n, hn, hcop⟩ := strictly_larger_coprime_binomial k m h₁.2
  exact ⟨n, hn.le, hcop⟩
