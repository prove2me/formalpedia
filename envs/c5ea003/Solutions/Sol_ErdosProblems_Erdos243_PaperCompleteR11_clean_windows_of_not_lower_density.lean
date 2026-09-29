-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.clean_windows_of_not_lower_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:33:55.195376+00:00
-- url     : https://prove2.me/submissions/ef1157a3-58e4-449a-a8ea-0ce8adc592f0

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_lowerDensityAtLeast_of_linear_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR9_disjoint_periodic_linear_bound
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Window incidences and quantitative exceptional density

Every hit is charged to an exceptional index together
with its offset. Overlapping windows therefore cost at most their length, not
the number of residue classes. No density assumption is hidden in the counting
lemmas. `LowerDensityAtLeast` uses the usual epsilon / eventual-prefix definition
of a lower bound for the lower asymptotic density (prefixes start at zero).
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR9
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (E : Set ℕ) (L : ℕ) (hL : 0 < L)
    (hnot : ¬ LowerDensityAtLeast E (1 / (L : ℝ))) :
    ∀ T : ℕ, ∃ n : ℕ, T ≤ n ∧ ∀ i : ℕ, i < L → n + i ∉ E := by
  classical
  intro T
  by_contra hn
  have hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ T + L * k + i ∈ E := by
    intro k
    by_contra hk
    apply hn
    refine ⟨T + L * k, by omega, ?_⟩
    intro i hi he
    exact hk ⟨i, hi, he⟩
  apply hnot
  apply lowerDensityAtLeast_of_linear_bound E 1 (L : ℝ) ((T + L : ℕ) : ℝ)
  · exact_mod_cast hL
  · intro X
    have h := disjoint_periodic_linear_bound E T L L hL (le_refl L) hhit X
    have hr : (X : ℝ) ≤ (L : ℝ) * (exceptionCount E X : ℝ) + ((T + L : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa only [one_mul] using hr
