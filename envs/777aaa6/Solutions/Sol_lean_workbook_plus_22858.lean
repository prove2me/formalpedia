-- Prove2me | solution 1 for lean_workbook_plus_22858
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:49:50.544042+00:00
-- url     : https://prove2.me/submissions/0a3b36e1-5ac1-4e69-994f-ed7048b71007

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.FieldTheory.Finite.Basic

theorem arbitrarily_large_prime_power_difference_indices (c : ℕ) (hc : 0 < c) (L : ℕ) :
    ∃ n : ℕ, L < n ∧ (c * n + 1).Prime ∧
      c * n + 1 ∣ (2 ^ c) ^ n - 1 := by
  obtain ⟨P, hP, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max 2 (1 + c * L)) hc.ne' (Nat.coprime_one_left c)
  have hP2 : 2 < P := lt_of_le_of_lt (le_max_left _ _) hP
  have hPL : 1 + c * L < P := lt_of_le_of_lt (le_max_right _ _) hP
  obtain ⟨n, hn⟩ := (Nat.modEq_iff_exists_eq_add (show 1 ≤ P by omega)).mp hmod.symm
  have hnL : L < n := by
    by_contra h
    have hle : n ≤ L := by omega
    have hm := Nat.mul_le_mul_left c hle
    omega
  have hcop : Nat.Coprime 2 P :=
    (Nat.coprime_of_lt_prime (by decide) hP2 hp).symm
  have hdiv : P ∣ 2 ^ (P - 1) - 1 :=
    Nat.dvd_of_mod_eq_zero (Nat.pow_card_sub_one_sub_one_mod_card hp hcop)
  refine ⟨n, hnL, ?_, ?_⟩
  · simpa only [hn, add_comm 1] using hp
  · simpa [hn, pow_mul, add_comm] using hdiv

theorem prime_power_difference_indices_infinite (c : ℕ) (hc : 0 < c) :
    {n : ℕ | 0 < n ∧ (c * n + 1).Prime ∧ c * n + 1 ∣ (2 ^ c) ^ n - 1}.Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro L
  obtain ⟨n, hn, hp, hd⟩ := arbitrarily_large_prime_power_difference_indices c hc L
  exact ⟨n, ⟨by omega, hp, hd⟩, hn⟩

theorem distinct_coprime_power_difference_infinitude (c : ℕ) (hc : 0 < c) :
    ∃ a b : ℕ, 0 < b ∧ b < a ∧ Nat.Coprime a b ∧
      {n : ℕ | 0 < n ∧ c * n + 1 ∣ a ^ n - b ^ n}.Infinite := by
  refine ⟨2 ^ c, 1, by decide, ?_, Nat.coprime_one_right _, ?_⟩
  · cases c with
    | zero => omega
    | succ c =>
      have hp := Nat.two_pow_pos c
      rw [pow_succ]
      omega
  · apply (prime_power_difference_indices_infinite c hc).mono
    intro n hn
    exact ⟨hn.1, by simpa using hn.2.2⟩

theorem solution (c : ℕ) :
    ∃ a b : ℕ, Nat.Coprime a b ∧ ∀ n : ℕ, 0 < n → c * n + 1 ∣ a ^ n - b ^ n := by
  exact ⟨1, 1, Nat.coprime_one_left _, fun _ _ => by simp⟩
