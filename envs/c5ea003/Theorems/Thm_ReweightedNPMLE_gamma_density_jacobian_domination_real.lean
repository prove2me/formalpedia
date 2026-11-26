-- Prove2me | Theorems.Thm_ReweightedNPMLE_gamma_density_jacobian_domination_real
-- name    : ReweightedNPMLE.gamma_density_jacobian_domination_real
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:17.261849+00:00
-- url     : https://prove2.me/theorems/05b05bb2-3185-4ae7-b3b5-3c03fab2a4a5
-- title:
--   Pointwise Gamma-density domination under a multiplicative change
-- statement:
--   Let $\rho_\alpha$ be the density of $n$ independent Gamma variables with shape and rate $\alpha>0$:
--   $$\rho_\alpha(w)=\prod_i\frac{\alpha^\alpha}{\Gamma(\alpha)}w_i^{\alpha-1}e^{-\alpha w_i}\quad(w_i>0).$$
--   Take $w_i>0$, $|t_i|\le1/8$, $c\ge0$, and a real $J$ satisfying $c\prod_i(1+t_i)\le J$. For $F_i=w_i(1+t_i)$,
--   $$
--   \rho_\alpha(w)c\,e^{-\alpha\{\sum_i(w_i-1)t_i+\sum_i t_i^2\}}
--   \le J\rho_\alpha(F).
--   $$
--   This is a deterministic density comparison. In applications $J$ can be an absolute Jacobian determinant, but the statement only assumes the displayed lower bound on $J$.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ChangeOfVariables.lean#L55-L100

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

theorem ReweightedNPMLE.gamma_density_jacobian_domination_real
    {n : ℕ} {α c J : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (w t : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ht : ∀ i, |t i| ≤ 1 / 8)
    (hdet : (∏ i, (1 + t i)) * c ≤ J) :
    gammaProductDensityReal n α α w *
        (c * Real.exp (-α *
          (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2))) ≤
      J * gammaProductDensityReal n α α
        (fun i ↦ w i * (1 + t i)) := by sorry
