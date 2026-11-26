-- Prove2me | Theorems.Thm_ReweightedNPMLE_abs_gaussianScore_le
-- name    : ReweightedNPMLE.abs_gaussianScore_le
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:02.642202+00:00
-- url     : https://prove2.me/theorems/99747b9f-4d33-4893-8040-df004f8a2289
-- title:
--   Uniform Gaussian-score bound on bounded location and observation sets
-- statement:
--   Let $x,\theta\in\mathbb R^d$ and $T,S\ge0$ satisfy $\|x\|\le T$ and $\|\theta\|\le S$. For the Gaussian score $s(x,\theta)=\langle x,\theta\rangle-\|\theta\|^2/2$, $$|s(x,\theta)|\le TS+S^2/2.$$ This uniform bound controls the exponential representation of the Gaussian kernel on bounded sets.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Gaussian.lean#L303-L318

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian

/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE

theorem ReweightedNPMLE.abs_gaussianScore_le {d : ℕ} {x θ : Point d} {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) :
    |gaussianScore x θ| ≤ T * S + S ^ 2 / 2 := by sorry
