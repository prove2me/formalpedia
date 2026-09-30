-- Prove2me | solution 1 for lean_workbook_plus_80616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:30:23.201738+00:00
-- url     : https://prove2.me/submissions/c8449e7b-dce0-4b98-aed7-5962aaa2e5ff

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SimultaneousApproximation

theorem same_bin_error (a b : ℝ) (M : ℕ) (hM : 0 < M)
    (h : ⌊Int.fract a * M⌋₊ = ⌊Int.fract b * M⌋₊) :
    |Int.fract a - Int.fract b| < 1 / M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have ha : 0 ≤ Int.fract a * M := mul_nonneg (Int.fract_nonneg a) hMr.le
  have hb : 0 ≤ Int.fract b * M := mul_nonneg (Int.fract_nonneg b) hMr.le
  have hi : ⌊Int.fract a * M⌋ = ⌊Int.fract b * M⌋ := by
    rw [← Int.natCast_floor_eq_floor ha, ← Int.natCast_floor_eq_floor hb, h]
  have he := Int.abs_sub_lt_one_of_floor_eq_floor hi
  rw [← sub_mul, abs_mul, abs_of_pos hMr] at he
  exact (lt_div_iff₀ hMr).2 he

theorem bounded_denominator (k : ℕ) (x : Fin k → ℝ) (M : ℕ) (hM : 0 < M) :
    ∃ n : ℕ, 0 < n ∧ n ≤ M ^ k ∧
      ∀ i : Fin k, ∃ m : ℤ, |(n : ℝ) * x i - m| < 1 / M := by
  classical
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let bin : Fin (M ^ k + 1) → Fin k → Fin M := fun n i =>
    ⟨⌊Int.fract ((n : ℝ) * x i) * M⌋₊,
      (Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hMr.le)).2
        (by nlinarith only [Int.fract_lt_one ((n : ℝ) * x i), hMr])⟩
  have hc : Fintype.card (Fin k → Fin M) < Fintype.card (Fin (M ^ k + 1)) := by
    simp
  obtain ⟨a, b, hab, hne⟩ :=
    Function.not_injective_iff.mp (Fintype.not_injective_of_card_lt bin hc)
  have pair_result (a b : Fin (M ^ k + 1)) (hlt : a < b) (heq : bin a = bin b) :
      ∃ n : ℕ, 0 < n ∧ n ≤ M ^ k ∧
        ∀ i : Fin k, ∃ m : ℤ, |(n : ℝ) * x i - m| < 1 / M := by
    refine ⟨b.val - a.val, by omega, by omega, ?_⟩
    intro i
    refine ⟨⌊(b : ℝ) * x i⌋ - ⌊(a : ℝ) * x i⌋, ?_⟩
    have he : ⌊Int.fract ((b : ℝ) * x i) * M⌋₊ =
        ⌊Int.fract ((a : ℝ) * x i) * M⌋₊ :=
      congrArg Fin.val (congrFun heq.symm i)
    have he' := same_bin_error ((b : ℝ) * x i) ((a : ℝ) * x i) M hM he
    convert he' using 1
    congr 1
    rw [Nat.cast_sub (Nat.le_of_lt hlt)]
    simp only [Int.fract, Int.cast_sub]
    ring
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact pair_result a b hlt hab
  · exact pair_result b a hlt hab.symm

theorem positive_denominator (k : ℕ) (x : Fin k → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : Fin k, ∃ m : ℤ, |(n : ℝ) * x i - m| < ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  have hMp : 0 < M := by
    have : (0 : ℝ) < M := lt_trans (one_div_pos.mpr hε) hM
    exact_mod_cast this
  have hMe : (1 : ℝ) / M < ε := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hMp
    apply (div_lt_iff₀ hMr).2
    simpa only [mul_comm] using (div_lt_iff₀ hε).1 hM
  obtain ⟨n, hn, _, hm⟩ := bounded_denominator k x M hMp
  exact ⟨n, hn, fun i => (hm i).imp fun _ h => h.trans hMe⟩

theorem arbitrarily_large_denominator (k : ℕ) (x : Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ ∀ i : Fin k, ∃ m : ℤ, |(n : ℝ) * x i - m| < ε := by
  obtain ⟨q, hq, hm⟩ := positive_denominator k (fun i => (N + 1 : ℕ) * x i) ε hε
  refine ⟨q * (N + 1), ?_, ?_⟩
  · nlinarith
  · intro i
    obtain ⟨m, hm⟩ := hm i
    refine ⟨m, ?_⟩
    simpa only [Nat.cast_mul, mul_assoc] using hm

theorem infinitely_many_denominators (k : ℕ) (x : Fin k → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    Set.Infinite {n : ℕ | 0 < n ∧
      ∀ i : Fin k, ∃ m : ℤ, |(n : ℝ) * x i - m| < ε} := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨n, hn, hm⟩ := arbitrarily_large_denominator k x ε hε N
  exact ⟨n, ⟨lt_of_le_of_lt (Nat.zero_le N) hn, hm⟩, hn⟩

end SimultaneousApproximation

theorem solution (k : ℕ) (x : Fin k → ℝ) (ε : ℝ) (ε_pos : ε > 0) :
    ∃ n : ℕ, ∀ i : Fin k, ∃ m : ℤ, abs (n * x i - m) < ε := by
  obtain ⟨n, _, hn⟩ := SimultaneousApproximation.positive_denominator k x ε ε_pos
  exact ⟨n, hn⟩

#print axioms SimultaneousApproximation.same_bin_error
#print axioms SimultaneousApproximation.bounded_denominator
#print axioms SimultaneousApproximation.positive_denominator
#print axioms SimultaneousApproximation.arbitrarily_large_denominator
#print axioms SimultaneousApproximation.infinitely_many_denominators
#print axioms solution
