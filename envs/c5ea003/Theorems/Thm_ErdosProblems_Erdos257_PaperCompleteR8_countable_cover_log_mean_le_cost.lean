-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_countable_cover_log_mean_le_cost
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.countable_cover_log_mean_le_cost
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:10:13.265079+00:00
-- url     : https://prove2.me/theorems/45128ef8-9566-42b5-9ead-c2410b279147
-- title:
--   Countable frame covers bound logarithmic means
-- statement:
--   For a finite support F covered by countably many finite frames G_j, with positive subprobability weights η_j summing to 1, exponents 0<α_j≤1, and nonnegative summable divisor-majorant costs c_j satisfying the stated framewise power bounds, the average of e·log of the divisor count from F over 1,…,X is at most the displayed sum of weighted frame costs, whenever X>0 and that sum is summable.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/CountableCoverLogBudget.lean#L129-L204
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
# Countable positive-cover first logarithmic moment

A finite test support admits a finite subcover. The omitted frame weights
are retained as a subprobability inequality, so no renormalisation cost is
lost. Countable divisor majorants are truncated only at the actual finite
observation horizon; their reciprocal costs are bounded by their convergent
series. The endpoint assumes summability of the explicit total cover cost,
not the logarithmic obstruction it proves.
-/
noncomputable section
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7

open ErdosProblems.Erdos257.PaperCompleteR8

theorem ErdosProblems.Erdos257.PaperCompleteR8.countable_cover_log_mean_le_cost
    (F : Finset ℕ) (G : ℕ → Finset ℕ) (η α : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (X : ℕ) (hX : 0 < X)
    (hη : HasSum η 1) (hηpos : ∀ j, 0 < η j)
    (hα : ∀ j, 0 < α j ∧ α j ≤ 1)
    (hc : ∀ j d, 0 < d → 0 ≤ c j d)
    (hcolumn : ∀ j, Summable (fun d : ℕ => c j d / (d : ℝ)))
    (hcover : ∀ a ∈ F, ∃ j, a ∈ G j)
    (hmaj : ∀ j n, 0 < n →
      (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j ≤ ∑ d ∈ n.divisors, c j d)
    (hcost : Summable (fun j => (∑' d : ℕ, c j d / (d : ℝ)) /
      (η j ^ α j) / ((2 : ℝ) ^ α j - 1))) :
    (∑ n ∈ Finset.Icc 1 X,
      Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) / X ≤
      ∑' j, (∑' d : ℕ, c j d / (d : ℝ)) /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by sorry
end
