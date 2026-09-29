-- Prove2me | solution 1 for ErdosProblems.Erdos257.cesaro_le_divisorMajorantCost
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:55:21.411688+00:00
-- url     : https://prove2.me/submissions/572f6b4e-8906-4458-b920-a56221c2b531

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Theorems.Thm_ErdosProblems_Erdos257_card_Icc_one_filter_dvd
import Mathlib

/-!
# Cover-independent periodic means

Lemma A.1 of the 2026-09-06 Type B revision return: a nonnegative divisor
majorant of `g` controls every Cesàro average of `g`, hence every periodic
mean. This is not an irrationality theorem. It bounds cover cost.

The coprime-cover obstruction (Type B Theorem B.1) uses this averaging plus
the elementary density `1 - ∏(1 - 1/a)`; that density identity is recorded
as an ordinary proof in `VariableExponentCoverSeparation.md`.
-/

namespace ErdosProblems.Erdos257
open Finset
end ErdosProblems.Erdos257

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
theorem solution
    (g : ℕ → ℝ) (D : Finset ℕ) (c : ℕ → ℝ) (X : ℕ)
    (hX : 0 < X)
    (hD : ∀ d ∈ D, 0 < d)
    (hc : ∀ d ∈ D, 0 ≤ c d)
    (hg0 : ∀ n, 0 ≤ g n)
    (hmaj : ∀ n, 0 < n → g n ≤ ∑ d ∈ D.filter (fun d => d ∣ n), c d) :
    (∑ n ∈ Icc 1 X, g n) / X ≤ divisorMajorantCost D c := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hsum :
      ∑ n ∈ Icc 1 X, g n ≤ ∑ d ∈ D, c d * (X / d : ℕ) := by
    calc
      ∑ n ∈ Icc 1 X, g n
          ≤ ∑ n ∈ Icc 1 X, ∑ d ∈ D.filter (fun d => d ∣ n), c d := by
            apply sum_le_sum
            intro n hn
            have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
            exact hmaj n (Nat.succ_le_iff.mp hn1)
      _ = ∑ n ∈ Icc 1 X, ∑ d ∈ D, (if d ∣ n then c d else 0) := by
            apply sum_congr rfl
            intro n hn
            simp [sum_filter]
      _ = ∑ d ∈ D, ∑ n ∈ Icc 1 X, (if d ∣ n then c d else 0) := by
            rw [sum_comm]
      _ = ∑ d ∈ D, c d * ((Icc 1 X).filter (fun n => d ∣ n)).card := by
            apply sum_congr rfl
            intro d hd
            have hconst :
                ∑ n ∈ Icc 1 X, (if d ∣ n then c d else 0) =
                  c d * ((Icc 1 X).filter (fun n => d ∣ n)).card := by
              rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
            simpa using hconst
      _ = ∑ d ∈ D, c d * (X / d : ℕ) := by
            apply sum_congr rfl
            intro d hd
            rw [card_Icc_one_filter_dvd (hD d hd)]
  have hdiv :
      (∑ d ∈ D, c d * (X / d : ℕ)) / X ≤ divisorMajorantCost D c := by
    unfold divisorMajorantCost
    rw [sum_div]
    apply sum_le_sum
    intro d hd
    have hXne : (X : ℝ) ≠ 0 := ne_of_gt hXpos
    calc
      c d * ((X / d : ℕ) : ℝ) / X
          ≤ c d * ((X : ℝ) / d) / X := by
            gcongr
            · exact hc d hd
            · exact Nat.cast_div_le
      _ = c d / d := by
            field_simp [hXne]
  exact (div_le_div_of_nonneg_right hsum hXpos.le).trans hdiv
