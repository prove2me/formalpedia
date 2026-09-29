-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.kernelWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:45:40.273567+00:00
-- url     : https://prove2.me/submissions/cafb72bd-452c-45cc-8a41-d517452b9cc3

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_kernel_den_pos
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Actual finite dyadic observation means

Round 8 proof text against Lean 4.29.1 / Mathlib
5e932f97dd25535344f80f9dd8da3aab83df0fe6. NOT COMPILED in this return.
The average samples exactly the positive progression points (m+1)*L.
No independently chosen existential return is substituted for an average.
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
theorem solution {B : ℝ} (hB : 1 < B) (d n : ℕ) :
    0 ≤ kernelWeight B d n := by
  by_cases hd : d = 0
  · subst d
    simp only [kernelWeight, pow_zero, sub_self, div_zero, le_refl]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hBpos : 0 < B := lt_trans zero_lt_one hB
    exact div_nonneg (pow_nonneg hBpos.le _) (kernel_den_pos hB hdpos).le
end
