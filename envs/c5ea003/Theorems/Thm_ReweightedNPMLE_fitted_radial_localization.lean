-- Prove2me | Theorems.Thm_ReweightedNPMLE_fitted_radial_localization
-- name    : ReweightedNPMLE.fitted_radial_localization
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:45:48.5678+00:00
-- url     : https://prove2.me/theorems/c2df4ac1-5199-4048-bf88-b01d0d34f58b
-- title:
--   Radial localization bounds for near-optimal fitted vectors
-- statement:
--   Let $n\ge1$, let $C\subset(0,\infty)^n$ be convex, and let $v_0$ maximize $L_{\mathbf1}(v)=\sum_i\log v_i$ on $C$. Suppose every relative vector $v/v_0-\mathbf1$, $v\in C$, is within Euclidean distance $\eta\ge0$ of a linear subspace $V$. Write $P_V$ for orthogonal projection, $\delta=w-\mathbf1$, $a=\|P_V\delta\|_2$, and $e=\eta\|\delta\|_2$. Assume
--   $$
--   \|\delta\|_\infty\le1/16,\quad a\le1/384,\quad e\le1/6144,\quad 0\le\tau<1/3072.
--   $$
--   For every $v\in C$ with $L_w(v)\ge L_w(v_0)-\tau$, let $z_i=\log(v_i/v_{0i})$. Then
--   $$
--   \begin{aligned}
--   \|z\|_\infty&\le1/8,\\
--   0\le L_{\mathbf1}(v_0)-L_{\mathbf1}(v)&\le37a^2+13e+13\tau,\\
--   \|z\|_2^2&\le72a^2+24e+24\tau,\\
--   \sum_i\delta_i z_i&\le37a^2+13e+12\tau.
--   \end{aligned}
--   $$
--   These simultaneous bounds quantify how small weight perturbations and approximation error control ordinary likelihood and fitted log-ratios.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedLocalization.lean#L76-L141

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedLocalization
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Likelihood-facing radial localization

Relative feasible fitted vectors and their log-ratios translate the radial
localization inequalities into ordinary likelihood loss and fitted-log
error.  The theorem applies simultaneously to every near-optimal fit.
-/

open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.fitted_radial_localization {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (v₀ : Fin n → ℝ) (hv₀ : IsMaxOn C (weightedLogLikelihood 1) v₀)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ) (hη : 0 ≤ η)
    (hwidth : ∀ u ∈ relativeFittedSet C v₀,
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η)
    (w v : Fin n → ℝ) (hv : v ∈ C) (τ : ℝ) (hτ₀ : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ≤ (1 / 16 : ℝ) / 24)
    (hE : η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖ ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : weightedLogLikelihood w v₀ - τ ≤ weightedLogLikelihood w v) :
    let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
    let E := η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
    (∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8) ∧
    0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
    weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤ 37 * A ^ 2 + 13 * E + 13 * τ ∧
    (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤ 72 * A ^ 2 + 24 * E + 24 * τ ∧
    (∑ i, (w i - 1) * fittedLogRatio v₀ v i) ≤ 37 * A ^ 2 + 13 * E + 12 * τ := by sorry
