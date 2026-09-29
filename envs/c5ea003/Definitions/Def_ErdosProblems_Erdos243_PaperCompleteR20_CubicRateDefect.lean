-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
-- name    : ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T19:23:41.568984+00:00
-- url     : https://prove2.me/theorems/ddce0c2a-32fd-4445-817e-92f197f123b5
-- title:
--   Cubic ratio error
-- statement:
--   Defines cubicRatioError for a real sequence C at an index n; its exact expression is in the pinned source.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDefect.lean#L1-L72
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Mathlib

/-!
# Erdős 243: from ratio little-o to additive cubic defect

The paper states the rate multiplicatively.  This file records the exact
rescaling that converts its `o(n^-3)` error into an additive error tending to
zero once the numerator has cubic size.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open Filter

def cubicRatioError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) / C n - (1 + 3 / (n : ℝ))










end ErdosProblems.Erdos243.PaperCompleteR20


