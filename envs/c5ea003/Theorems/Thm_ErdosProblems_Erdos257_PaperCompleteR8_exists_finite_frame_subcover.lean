-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_finite_frame_subcover
-- name    : ErdosProblems.Erdos257.PaperCompleteR8.exists_finite_frame_subcover
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:10:10.023736+00:00
-- url     : https://prove2.me/theorems/0ef7e9b1-335c-4896-a671-3d8663dac8d4
-- title:
--   Finite sets admit finite subcovers by frames
-- statement:
--   If each element of a finite set F lies in some frame G_j from a countable family, then a finite collection of frame indices already covers F.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/PaperCompleteR8/CountableCoverLogBudget.lean#L108-L127
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

theorem ErdosProblems.Erdos257.PaperCompleteR8.exists_finite_frame_subcover (F : Finset ℕ) (G : ℕ → Finset ℕ)
    (hcover : ∀ a ∈ F, ∃ j, a ∈ G j) :
    ∃ J : Finset ℕ, F ⊆ J.biUnion G := by sorry
end
