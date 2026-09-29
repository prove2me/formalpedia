-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.lowerDensityAtLeast_iff_of_eventual_iff
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:16:41.944297+00:00
-- url     : https://prove2.me/submissions/341bce3d-c0a2-43c3-a1b1-e5f10e9a565d

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_LowerDensityAtLeast_of_eventual_subset
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
theorem solution (E F : Set ℕ) (T : ℕ) (d : ℝ)
    (heq : ∀ n, T ≤ n → (n ∈ E ↔ n ∈ F)) :
    LowerDensityAtLeast E d ↔ LowerDensityAtLeast F d := by
  constructor
  · intro h
    exact h.of_eventual_subset T (fun n hn ↦ (heq n hn).mp)
  · intro h
    exact h.of_eventual_subset T (fun n hn ↦ (heq n hn).mpr)
