-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
-- name    : ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:57:58.719096+00:00
-- url     : https://prove2.me/theorems/cb9eb596-2050-4141-ae92-3c34f9bc85a4
-- title:
--   Real forward differences and rising cubic
-- statement:
--   Defines forward differences of real sequences, their iterates and the real function n(n + 1)(n + 2).
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDifferenceLimits.lean#L1-L118
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Mathlib

/-!
# Erdős 243: limit transport for the cubic finite-difference extraction

The paper's analytic comparison produces a residual whose first forward
difference tends to zero.  This file proves that this is exactly enough for
the fourth difference of the integer numerator to tend to zero, because the
rising cubic has identically zero fourth difference.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def realForwardDiff (u : ℕ → ℝ) (n : ℕ) : ℝ := u (n + 1) - u n

def iterRealForwardDiff : ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, u => u
  | k + 1, u => realForwardDiff (iterRealForwardDiff k u)















/-- The rising cubic used in the paper. -/
def risingCubic (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (n + 2)








end ErdosProblems.Erdos243.PaperCompleteR20


