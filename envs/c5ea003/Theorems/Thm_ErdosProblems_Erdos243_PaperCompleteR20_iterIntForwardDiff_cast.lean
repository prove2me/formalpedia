-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterIntForwardDiff_cast
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.iterIntForwardDiff_cast
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:56:25.923419+00:00
-- url     : https://prove2.me/theorems/a3257090-59b9-441d-82d0-a8584c5a37d2
-- title:
--   Lean source theorem: iterIntForwardDiff_cast
-- statement:
--   Taking the k-fold forward difference of an integer-valued sequence and then casting to the reals agrees pointwise with first casting the sequence and then taking the k-fold real forward difference.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDifferenceLimits.lean#L63-L70
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Mathlib

/-!
# Erdős 243: limit transport for the cubic finite-difference extraction

The paper's analytic comparison produces a residual whose first forward
difference tends to zero.  This file proves that this is exactly enough for
the fourth difference of the integer numerator to tend to zero, because the
rising cubic has identically zero fourth difference.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.iterIntForwardDiff_cast (k : ℕ) (u : ℕ → ℤ) (n : ℕ) :
    (iterIntForwardDiff k u n : ℝ) =
      iterRealForwardDiff k (fun j => (u j : ℝ)) n := by sorry
