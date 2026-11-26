-- Prove2me | Theorems.Thm_ReweightedNPMLE_multiplicativeChange_injOn_of_monotone
-- name    : ReweightedNPMLE.multiplicativeChange_injOn_of_monotone
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:30.938101+00:00
-- url     : https://prove2.me/theorems/e415b483-4de8-572c-bcc5-339f5cd1d785
-- title:
--   Injectivity of a positive multiplicative perturbation with a monotone field
-- statement:
--   Let $S\subset(0,\infty)^n$ and let $t:\mathbb R^n\to\mathbb R^n$ satisfy $1+t_i(w)>0$ for every $w\in S$ and every coordinate. Suppose $t$ is monotone on $S$ in the sense that
--   $$\langle w-v,t(w)-t(v)\rangle\ge0\qquad(w,v\in S).$$
--   Then the coordinatewise multiplicative map
--   $$F_i(w)=w_i\{1+t_i(w)\}$$
--   is injective on $S$. The hypotheses impose neither convexity of $S$ nor continuity or differentiability of $t$. Positivity and monotonicity alone rule out two distinct points having the same transformed vector.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ChangeOfVariables.lean#L280-L329

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

theorem ReweightedNPMLE.multiplicativeChange_injOn_of_monotone
    {n : ℕ} {s : Set (Fin n → ℝ)}
    (t : (Fin n → ℝ) → (Fin n → ℝ))
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (htpos : ∀ w ∈ s, ∀ i, 0 < 1 + t w i)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i)) :
    Set.InjOn (fun w i ↦ w i * (1 + t w i)) s := by sorry
