-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.progressionMean_mono
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:01:27.964221+00:00
-- url     : https://prove2.me/submissions/f1096956-3160-41d6-99bb-ffc5549bf7c6

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
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
theorem solution (L T : ℕ) (f g : ℕ → ℝ)
    (hfg : ∀ n, f n ≤ g n) : progressionMean L T f ≤ progressionMean L T g := by
  unfold progressionMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun m _ => hfg _)) (Nat.cast_nonneg T)
end
