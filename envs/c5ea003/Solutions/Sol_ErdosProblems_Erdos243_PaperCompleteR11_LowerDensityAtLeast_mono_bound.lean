-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast.mono_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:20:29.875929+00:00
-- url     : https://prove2.me/submissions/cd20a9c9-650f-4417-a7ea-e6371ad7934f

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
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
theorem solution {E : Set ℕ} {a b : ℝ}
    (h : LowerDensityAtLeast E b) (hab : a ≤ b) : LowerDensityAtLeast E a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun X hX ↦ ?_⟩
  calc
    (a - ε) * (X : ℝ) ≤ (b - ε) * (X : ℝ) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hab ε) (Nat.cast_nonneg X)
    _ ≤ (exceptionCount E X : ℝ) := hN X hX
