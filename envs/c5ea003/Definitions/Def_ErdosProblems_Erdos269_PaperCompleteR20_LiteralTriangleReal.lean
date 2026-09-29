-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangleReal
-- name    : ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangleReal
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:15:46.885961+00:00
-- url     : https://prove2.me/theorems/7ce13c13-02e1-4360-a1f3-ee72f0bdce8f
-- title:
--   LiteralTriangleReal
-- statement:
--   Defines real logarithmic coordinates and phase weights for literal triangle points, a rectangular subset side length, and a positive denominator for quadratic triangle-size estimates.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/LiteralTriangleReal.lean#L1-L212
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_BoundedRadixTailEscape
import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_DyadicOrderedTailRecurrence
import Definitions.Def_ErdosProblems_Erdos269_DyadicShellSummability
import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_LiteralTriangle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Exact logarithmic coordinates and the paper's rectangle lower bound. -/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators

noncomputable def triangleLogPoint (v : ℕ × ℕ) : ℝ :=
  (v.1 : ℝ) * Real.logb 2 3 + (v.2 : ℝ) * Real.logb 2 5

noncomputable def triangleTheta (p : ℕ) : ℝ := 1 / Real.logb 2 p

















noncomputable def literalLogWeight (a : ℕ) (v : ℕ × ℕ) : ℕ :=
  3 ^ (⌊((a : ℝ) + 1) * triangleTheta 3⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 3⌋₊) *
  5 ^ (⌊((a : ℝ) + 1) * triangleTheta 5⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 5⌋₊)





noncomputable def triangleRectangleSide (a p : ℕ) : ℕ :=
  ⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊ + 1







noncomputable def triangleQuadraticDenominator : ℝ :=
  (2 * Real.logb 2 3 + 1) * (2 * Real.logb 2 5 + 1)










end ErdosProblems.Erdos269.PaperCompleteR20


