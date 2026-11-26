-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_max_coordinate_concentration
-- name    : ReweightedNPMLE.gamma_max_coordinate_concentration
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:46:38.920801+00:00
-- url     : https://prove2.me/theorems/9f04491e-713e-4366-b799-e3eb6c798c8a
-- title:
--   Maximum-coordinate concentration for independent Gamma weights
-- statement:
--   Let $W_1,\ldots,W_n$ be independent $\operatorname{Gamma}(a,a)$ variables with $a>0$. For $0<t\le1$, $$\Pr\bigl(\exists i:\ |W_i-1|>t\bigr)\le2n e^{-at^2/4}.$$ The statement allows $n=0$, in which case the event is empty. This estimate is used in both reweighting regimes.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L623-L652

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

theorem ReweightedNPMLE.gamma_max_coordinate_concentration {n : ℕ} {a t : ℝ}
    (ha : 0 < a) (ht₀ : 0 < t) (ht₁ : t ≤ 1) :
    (Measure.pi (fun _ : Fin n ↦ gammaMeasure a a)).real
        {w | ∃ i, |w i - 1| > t} ≤
      2 * n * Real.exp (-a * t ^ 2 / 4) := by sorry
