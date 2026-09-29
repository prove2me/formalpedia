-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.exists_finite_frame_subcover
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:41:46.865593+00:00
-- url     : https://prove2.me/submissions/54ae63e1-ba9e-48c6-accb-f6e9fd643096

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Mathlib
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos257.PaperCompleteR8
end ErdosProblems.Erdos257.PaperCompleteR8

/-!
# Countable positive-cover first logarithmic moment

A finite test support admits a finite subcover. The omitted frame weights
are retained as a subprobability inequality, so no renormalisation cost is
lost. Countable divisor majorants are truncated only at the actual finite
observation horizon; their reciprocal costs are bounded by their convergent
series. The endpoint assumes summability of the explicit total cover cost,
not the logarithmic obstruction it proves.
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
theorem solution (F : Finset ℕ) (G : ℕ → Finset ℕ)
    (hcover : ∀ a ∈ F, ∃ j, a ∈ G j) :
    ∃ J : Finset ℕ, F ⊆ J.biUnion G := by
  classical
  revert hcover
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp⟩
  | @insert a F ha ih =>
    intro hcover
    obtain ⟨j, hj⟩ := hcover a (Finset.mem_insert_self a F)
    obtain ⟨J, hJ⟩ := ih (fun b hb => hcover b (Finset.mem_insert_of_mem hb))
    refine ⟨insert j J, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_insert_self _ _, hj⟩
    · obtain ⟨k, hk, hbk⟩ := Finset.mem_biUnion.mp (hJ hb)
      exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_insert_of_mem hk, hbk⟩
end
