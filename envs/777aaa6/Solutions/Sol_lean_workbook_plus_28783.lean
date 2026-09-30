-- Prove2me | solution 1 for lean_workbook_plus_28783
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:17:39.037294+00:00
-- url     : https://prove2.me/submissions/4e7ee4b5-338f-4f38-ba8c-bab63ee7a4f6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.ModEq

namespace ShiftedRepunitMultiple

theorem positive_power_collision (b M : ℕ) (hb : 1 < b) (hM : 0 < M) :
    ∃ i j : ℕ, 0 < i ∧ i < j ∧ M ∣ b ^ j - b ^ i := by
  let f : ℕ → Fin M := fun k => ⟨b ^ (k + 1) % M, Nat.mod_lt _ hM⟩
  obtain ⟨i, j, hij, hsame⟩ := Finite.exists_ne_map_eq_of_infinite f
  have hmod : b ^ (i + 1) ≡ b ^ (j + 1) [MOD M] := congrArg Fin.val hsame
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hlt : i + 1 < j + 1 := by omega
    exact ⟨i + 1, j + 1, by omega, hlt,
      (Nat.modEq_iff_dvd' (Nat.pow_lt_pow_right hb hlt).le).mp hmod⟩
  · have hlt : j + 1 < i + 1 := by omega
    exact ⟨j + 1, i + 1, by omega, hlt,
      (Nat.modEq_iff_dvd' (Nat.pow_lt_pow_right hb hlt).le).mp hmod.symm⟩

theorem difference_factorization (b i j : ℕ) (hij : i ≤ j) :
    b ^ i * (b ^ (j - i) - 1) = b ^ j - b ^ i := by
  rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_of_le hij]

theorem positive_multiple (b n : ℕ) (hb : 1 < b) (hn : 0 < n) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧
      0 < (b ^ k * (b ^ m - 1)) / (b - 1) ∧
      n ∣ (b ^ k * (b ^ m - 1)) / (b - 1) := by
  have hb1 : 0 < b - 1 := Nat.sub_pos_of_lt hb
  obtain ⟨i, j, hi, hij, hd⟩ :=
    positive_power_collision b ((b - 1) * n) hb (Nat.mul_pos hb1 hn)
  obtain ⟨q, hq⟩ := hd
  have hdiff : 0 < b ^ j - b ^ i := Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hb hij)
  have hprod : 0 < ((b - 1) * n) * q := by omega
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0, mul_zero] at hprod
    exact (lt_irrefl 0) hprod
  have hvalue : (b ^ i * (b ^ (j - i) - 1)) / (b - 1) = n * q := by
    rw [difference_factorization b i j hij.le, hq, Nat.mul_assoc,
      Nat.mul_div_right _ hb1]
  refine ⟨i, j - i, hi, Nat.sub_pos_of_lt hij, ?_, ?_⟩
  · rw [hvalue]
    exact Nat.mul_pos hn hqpos
  · exact ⟨q, hvalue⟩

theorem decimal_positive_multiple (n : ℕ) (hn : 0 < n) :
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ 0 < (10 ^ k * (10 ^ m - 1)) / 9 ∧
      n ∣ (10 ^ k * (10 ^ m - 1)) / 9 := by
  simpa using positive_multiple 10 n (by decide) hn

end ShiftedRepunitMultiple

theorem solution (n : ℕ) : ∃ k m : ℕ, n ∣ (10 ^ k * (10 ^ m - 1)) / 9 := by
  by_cases hn : n = 0
  · subst n
    exact ⟨0, 0, by simp⟩
  · obtain ⟨k, m, _, _, _, hd⟩ :=
      ShiftedRepunitMultiple.decimal_positive_multiple n (Nat.pos_of_ne_zero hn)
    exact ⟨k, m, hd⟩
