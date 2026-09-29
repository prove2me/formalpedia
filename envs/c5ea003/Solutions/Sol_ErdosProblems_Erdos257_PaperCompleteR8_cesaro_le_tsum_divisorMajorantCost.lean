-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.cesaro_le_tsum_divisorMajorantCost
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:57:47.557508+00:00
-- url     : https://prove2.me/submissions/006295c4-f248-47bb-aac0-cc6db9f5097e

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Theorems.Thm_ErdosProblems_Erdos257_cesaro_le_divisorMajorantCost
import Mathlib
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos257.PaperCompleteR8
end ErdosProblems.Erdos257.PaperCompleteR8

/-!
# Countable positive-cover first logarithmic moment

A finite test support admits a finite subcover. The omitted frame weights
are retained as a subprobability inequality, so no renormalisation cost is
lost. Countable divisor majorants are truncated only at the actual finite
observation horizon; their reciprocal costs are bounded by their convergent
series. The endpoint assumes summability of the explicit total cover cost,
not the logarithmic obstruction it proves.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution
    (g c : ℕ → ℝ) (X : ℕ) (hX : 0 < X)
    (hg : ∀ n, 0 ≤ g n) (hc : ∀ d, 0 < d → 0 ≤ c d)
    (hs : Summable (fun d : ℕ => c d / (d : ℝ)))
    (hmaj : ∀ n, 0 < n → g n ≤ ∑ d ∈ n.divisors, c d) :
    (∑ n ∈ Finset.Icc 1 X, g n) / X ≤ ∑' d : ℕ, c d / (d : ℝ) := by
  classical
  let D := Finset.Icc 1 X
  let gX : ℕ → ℝ := fun n => if n ≤ X then g n else 0
  have hD : ∀ d ∈ D, 0 < d := by
    intro d hd
    exact (Finset.mem_Icc.mp hd).1
  have htrunc : ∀ n, 0 < n →
      gX n ≤ ∑ d ∈ D.filter (fun d => d ∣ n), c d := by
    intro n hn
    by_cases hnx : n ≤ X
    · have hsub : n.divisors ⊆ D.filter (fun d => d ∣ n) := by
        intro d hd
        have hdn := Nat.dvd_of_mem_divisors hd
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
          ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd hn hdn).trans hnx⟩, hdn⟩
      have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun d hd _ => hc d (hD d (Finset.mem_filter.mp hd).1))
      simpa only [gX, if_pos hnx] using (hmaj n hn).trans hsum
    · simp only [gX, if_neg hnx]
      exact Finset.sum_nonneg (fun d hd => hc d (hD d (Finset.mem_filter.mp hd).1))
  have hfinite := cesaro_le_divisorMajorantCost gX D c X hX hD
    (fun d hd => hc d (hD d hd)) (fun n => by
      dsimp [gX]
      split_ifs
      · exact hg n
      · exact le_rfl) htrunc
  have heq : (∑ n ∈ Finset.Icc 1 X, gX n) = ∑ n ∈ Finset.Icc 1 X, g n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact if_pos (Finset.mem_Icc.mp hn).2
  rw [heq] at hfinite
  have hcost : divisorMajorantCost D c ≤ ∑' d : ℕ, c d / (d : ℝ) := by
    apply hs.sum_le_tsum D
    intro d _
    by_cases hd : d = 0
    · simp [hd]
    · exact div_nonneg (hc d (Nat.pos_of_ne_zero hd)) (Nat.cast_nonneg d)
  exact hfinite.trans hcost
end
