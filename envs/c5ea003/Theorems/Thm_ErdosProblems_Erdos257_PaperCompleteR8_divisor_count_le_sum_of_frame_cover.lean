-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_divisor_count_le_sum_of_frame_cover
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.divisor_count_le_sum_of_frame_cover
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:07:50.880993+00:00
-- url     : https://prove2.me/theorems/7d19fc80-94b6-4c31-80c5-3f22ac71d2a8
-- title:
--   A frame cover bounds the divisor count
-- statement:
--   If a finite set F is covered by the union of finitely many frames G_j, then the number of elements of F dividing n is at most the sum of the corresponding divisor counts in those frames.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/FiniteCoverLogBudget.lean#L61-L73
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

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
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.divisor_count_le_sum_of_frame_cover (F J : Finset ℕ)
    (G : ℕ → Finset ℕ) (hcover : F ⊆ J.biUnion G) (n : ℕ) :
    (F.filter (fun a => a ∣ n)).card ≤
      ∑ j ∈ J, ((G j).filter (fun a => a ∣ n)).card := by sorry
end
