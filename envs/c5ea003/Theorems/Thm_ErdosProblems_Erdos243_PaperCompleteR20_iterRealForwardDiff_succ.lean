-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_iterRealForwardDiff_succ
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_succ
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:49:39.920581+00:00
-- url     : https://prove2.me/theorems/f21a06a3-e6f6-4229-849e-c6aa12b0cf7e
-- title:
--   Successor step for iterated real forward differences
-- statement:
--   For every natural k and real sequence u, the (k + 1)-fold forward difference of u is the real forward difference of its k-fold forward difference.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDifferenceLimits.lean#L27-L28
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

@[simp] theorem ErdosProblems.Erdos243.PaperCompleteR20.iterRealForwardDiff_succ (k : ℕ) (u : ℕ → ℝ) :
    iterRealForwardDiff (k + 1) u = realForwardDiff (iterRealForwardDiff k u) := by sorry
