-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_const_mul
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_const_mul
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:00:26.390531+00:00
-- url     : https://prove2.me/theorems/305f3cef-04ad-46a8-8bfa-1cc63352c97b
-- title:
--   Lean source theorem: iterRealForwardDiff_const_mul
-- statement:
--   The k-fold real forward-difference operator commutes with multiplication of a real sequence by a constant.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDifferenceLimits.lean#L53-L61
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

theorem ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_const_mul (k : ℕ) (c : ℝ) (u : ℕ → ℝ) :
    iterRealForwardDiff k (fun n => c * u n) =
      fun n => c * iterRealForwardDiff k u n := by sorry
