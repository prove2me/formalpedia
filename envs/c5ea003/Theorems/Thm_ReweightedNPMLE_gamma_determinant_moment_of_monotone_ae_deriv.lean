-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_determinant_moment_of_monotone_ae_deriv
-- name    : ReweightedNPMLE.gamma_determinant_moment_of_monotone_ae_deriv
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:10.821212+00:00
-- url     : https://prove2.me/theorems/a8e165ed-9d5d-51f7-8d8d-7c4030ed58c3
-- title:
--   Determinant-moment inequality from a monotone Gamma transformation
-- statement:
--   Let $\alpha>0$, let $P_\alpha$ be the product Gamma law with shape and rate $\alpha$, and let $S\subset(0,\infty)^n$ be measurable. Let measurable maps $t:\mathbb R^n\to\mathbb R^n$ and $c:\mathbb R^n\to\mathbb R$ satisfy $c\ge0$, $|t_i|\le1/8$, and $\langle w-v,t(w)-t(v)\rangle\ge0$ on $S$. Assume $t$ is Fréchet differentiable Lebesgue-almost everywhere on $S$ and, there,
--   $$c(w)\prod_i(1+t_i(w))\le\left|\det\!\left[\operatorname{diag}(1+t(w))+\operatorname{diag}(w)Dt(w)\right]\right|.$$
--   Then
--   $$
--   \int_S c(w)\exp\!\left[-\alpha\{\langle w-\mathbf1,t(w)\rangle+\|t(w)\|_2^2\}\right]\,dP_\alpha(w)\le1.
--   $$
--   The assumptions permit exceptional points where differentiability or the determinant bound fails.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ChangeOfVariables.lean#L517-L554

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.gamma_determinant_moment_of_monotone_ae_deriv
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (t : (Fin n → ℝ) → (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (t' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (ht' : ∀ᵐ w ∂volume, w ∈ s → HasFDerivAt t (t' w) w)
    (htmeas : Measurable t) (hcmeas : Measurable c)
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (ht : ∀ w ∈ s, ∀ i, |t w i| ≤ 1 / 8)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i))
    (hc : ∀ w ∈ s, 0 ≤ c w)
    (hdet : ∀ᵐ w ∂volume, w ∈ s →
      (∏ i, (1 + t w i)) * c w ≤
        |(w • t' w + (1 + t w) •
          ContinuousLinearMap.id ℝ (Fin n → ℝ)).det|) :
    ∫⁻ w in s, ENNReal.ofReal
        (c w * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by sorry
