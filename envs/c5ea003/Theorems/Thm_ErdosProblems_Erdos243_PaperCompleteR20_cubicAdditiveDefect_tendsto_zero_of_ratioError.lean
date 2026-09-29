-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicAdditiveDefect_tendsto_zero_of_ratioError
-- name    : ErdosProblems.Erdos243.PaperCompleteR20.cubicAdditiveDefect_tendsto_zero_of_ratioError
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:32:25.554332+00:00
-- url     : https://prove2.me/theorems/3ff12abb-aab0-4f32-92c6-dd238ffd46e9
-- title:
--   Lean source theorem: cubicAdditiveDefect_tendsto_zero_of_ratioError
-- statement:
--   For a real sequence eventually nonzero, if C(n)/n³ tends to K and n³ times its error from the cubic model ratio 1+3/n tends to zero, then its additive cubic recurrence defect tends to zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Erdos243/PaperCompleteR20/CubicRateDefect.lean#L33-L48
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Mathlib

/-!
# Erdős 243: from ratio little-o to additive cubic defect

The paper states the rate multiplicatively.  This file records the exact
rescaling that converts its `o(n^-3)` error into an additive error tending to
zero once the numerator has cubic size.
-/

noncomputable section


open Filter

open ErdosProblems.Erdos243.PaperCompleteR20

theorem ErdosProblems.Erdos243.PaperCompleteR20.cubicAdditiveDefect_tendsto_zero_of_ratioError
    (C : ℕ → ℝ) (K : ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hcubic : Tendsto (fun n => C n / (n : ℝ) ^ 3) atTop (nhds K))
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    Tendsto (cubicAdditiveDefect C) atTop (nhds 0) := by sorry
