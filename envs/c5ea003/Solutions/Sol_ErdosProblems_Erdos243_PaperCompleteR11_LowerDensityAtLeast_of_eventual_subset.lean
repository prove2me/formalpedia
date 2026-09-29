-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast.of_eventual_subset
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:37:34.457528+00:00
-- url     : https://prove2.me/submissions/e2b2188b-da29-4c23-9f2e-b1f1bb489520

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_exceptionCount_le_of_eventual_subset
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
theorem solution {E F : Set ℕ} {d : ℝ}
    (hE : LowerDensityAtLeast E d) (T : ℕ)
    (hsub : ∀ n, T ≤ n → n ∈ E → n ∈ F) : LowerDensityAtLeast F d := by
  intro ε hε
  obtain ⟨N, hN⟩ := hE (ε / 2) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt ((2 * (T : ℝ)) / ε)
  refine ⟨max N M, ?_⟩
  intro X hX
  have hXN : N ≤ X := le_trans (le_max_left _ _) hX
  have hXM : (M : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast le_trans (le_max_right N M) hX
  have hsmall : 2 * (T : ℝ) < (X : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_lt_of_le hM hXM)
  have hc : (exceptionCount E X : ℝ) ≤ (T : ℝ) + (exceptionCount F X : ℝ) := by
    exact_mod_cast exceptionCount_le_of_eventual_subset E F T X hsub
  have hl := hN X hXN
  nlinarith
