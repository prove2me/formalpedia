-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.disjoint_periodic_lowerDensity
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:45:32.090385+00:00
-- url     : https://prove2.me/submissions/d20567c4-b72d-4355-aeb2-6a37547a6120

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_lowerDensityAtLeast_of_linear_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR9_disjoint_periodic_linear_bound
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Finite-prefix and constant transport for the literal
lower asymptotic density used throughout the R11 window arguments. -/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open ErdosProblems.Erdos243.PaperCompleteR9
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems.Erdos243.PaperCompleteR9
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (E : Set ℕ) (r s L : ℕ)
    (hs : 0 < s) (hL : L ≤ s)
    (hhit : ∀ k : ℕ, ∃ i : ℕ, i < L ∧ r + s * k + i ∈ E) :
    LowerDensityAtLeast E (1 / (s : ℝ)) := by
  apply lowerDensityAtLeast_of_linear_bound E 1 (s : ℝ) (r + s : ℕ)
    (by exact_mod_cast hs)
  intro X
  have h := disjoint_periodic_linear_bound E r s L hs hL hhit X
  simpa only [one_mul] using (show (X : ℝ) ≤
    (s : ℝ) * (exceptionCount E X : ℝ) + ((r + s : ℕ) : ℝ) by exact_mod_cast h)
