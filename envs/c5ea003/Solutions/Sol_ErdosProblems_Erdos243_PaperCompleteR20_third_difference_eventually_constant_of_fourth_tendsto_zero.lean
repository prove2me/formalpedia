-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.third_difference_eventually_constant_of_fourth_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:05:16.45884+00:00
-- url     : https://prove2.me/submissions/c15c8622-fee3-4915-93d7-a2cb10587e8e

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_eventually_constant_of_forwardDiff_eventually_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_eventually_eq_zero_of_intCast_tendsto_zero
import Mathlib

/-!
# Erdős 243: integer finite differences for the cubic-rate bridge

This file isolates the discrete integrality step in the proof of the paper's
cubic-rate theorem.  Once the analytic comparison with the rising-factorial
model shows that a sufficiently high finite difference tends to zero, its
integer values force it to vanish identically on a tail.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter











/-- The exact integrality conclusion used after the analytic finite-difference
estimate in the cubic-rate argument. -/
theorem eventually_iterIntForwardDiff_eq_zero
    (u : ℕ → ℤ) (k : ℕ)
    (h : Tendsto (fun n => (iterIntForwardDiff k u n : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, iterIntForwardDiff k u n = 0 :=
  eventually_eq_zero_of_intCast_tendsto_zero (iterIntForwardDiff k u) h
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℤ)
    (h : Tendsto (fun n => (iterIntForwardDiff 4 C n : ℝ)) atTop (nhds 0)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      iterIntForwardDiff 3 C n = iterIntForwardDiff 3 C N := by
  apply eventually_constant_of_forwardDiff_eventually_zero
  simpa [iterIntForwardDiff] using eventually_iterIntForwardDiff_eq_zero C 4 h
