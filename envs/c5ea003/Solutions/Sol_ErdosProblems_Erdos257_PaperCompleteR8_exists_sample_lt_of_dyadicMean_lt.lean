-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.exists_sample_lt_of_dyadicMean_lt
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:18:40.285067+00:00
-- url     : https://prove2.me/submissions/b9d9c011-df71-44a1-ac76-95397788aeb6

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR8_FiniteMeans
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR7_exists_lt_of_mean_lt
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
theorem solution
    (L R M : ℕ) (hM : 0 < M) (f : ℕ → ℝ) (c : ℝ)
    (hmean : dyadicMean L R M f < c) :
    ∃ j m : ℕ, R ≤ j ∧ j < R + M ∧ m < 2 ^ j ∧ f ((m + 1) * L) < c := by
  have hs : (Finset.Ico R (R + M)).Nonempty := by
    refine ⟨R, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
    omega
  have hcard : (Finset.Ico R (R + M)).card = M := by
    -- Mathlib/Order/Interval/Finset/Nat.lean: Nat.card_Ico.
    rw [Nat.card_Ico]
    omega
  have hout :
      (∑ j ∈ Finset.Ico R (R + M), progressionMean L (2 ^ j) f) /
        ((Finset.Ico R (R + M)).card : ℝ) < c := by
    rw [hcard]
    exact hmean
  obtain ⟨j, hj, hjmean⟩ := exists_lt_of_mean_lt
    (Finset.Ico R (R + M)) hs (fun j => progressionMean L (2 ^ j) f) hout
  have hT : 0 < (2 : ℕ) ^ j := by positivity
  have ht : (Finset.range (2 ^ j)).Nonempty :=
    ⟨0, Finset.mem_range.mpr hT⟩
  have hin :
      (∑ m ∈ Finset.range (2 ^ j), f ((m + 1) * L)) /
        ((Finset.range (2 ^ j)).card : ℝ) < c := by
    rw [Finset.card_range]
    exact hjmean
  obtain ⟨m, hm, hfm⟩ := exists_lt_of_mean_lt
    (Finset.range (2 ^ j)) ht (fun m => f ((m + 1) * L)) hin
  exact ⟨j, m, (Finset.mem_Ico.mp hj).1, (Finset.mem_Ico.mp hj).2,
    Finset.mem_range.mp hm, hfm⟩
end
