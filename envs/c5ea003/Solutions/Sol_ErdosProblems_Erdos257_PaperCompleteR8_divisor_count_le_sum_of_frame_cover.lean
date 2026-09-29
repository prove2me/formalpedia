-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.divisor_count_le_sum_of_frame_cover
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:55:19.394785+00:00
-- url     : https://prove2.me/submissions/7729ade1-b16d-4ce0-b522-8dbe5413e874

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
# Finite positive-cover logarithmic budget

The scalar logarithmic bound is combined with actual divisor-majorant
averaging. Frames may overlap: only domination of the incidence count by
the sum of frame counts is used. The family and each divisor majorant are
finite. This does not assert the countable-cover obstruction or construct
the infinite class-separating host.
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
theorem solution (F J : Finset ℕ)
    (G : ℕ → Finset ℕ) (hcover : F ⊆ J.biUnion G) (n : ℕ) :
    (F.filter (fun a => a ∣ n)).card ≤
      ∑ j ∈ J, ((G j).filter (fun a => a ∣ n)).card := by
  classical
  have hsub : F.filter (fun a => a ∣ n) ⊆
      J.biUnion (fun j => (G j).filter (fun a => a ∣ n)) := by
    intro a ha
    obtain ⟨haF, had⟩ := Finset.mem_filter.mp ha
    obtain ⟨j, hj, haG⟩ := Finset.mem_biUnion.mp (hcover haF)
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr ⟨haG, had⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le
end
