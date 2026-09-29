-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.dyadicMean_mono
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:02:48.285733+00:00
-- url     : https://prove2.me/submissions/64ba8fd4-bc82-4dca-a7d3-15344c67380b

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_progressionMean_mono
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
theorem solution (L R M : ℕ) (f g : ℕ → ℝ)
    (hfg : ∀ n, f n ≤ g n) : dyadicMean L R M f ≤ dyadicMean L R M g := by
  unfold dyadicMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun j _ => progressionMean_mono L _ f g hfg))
    (Nat.cast_nonneg M)
end
