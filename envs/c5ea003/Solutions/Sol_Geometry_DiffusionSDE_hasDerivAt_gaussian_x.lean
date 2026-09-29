-- Prove2me | solution 1 for Geometry.DiffusionSDE.hasDerivAt_gaussian_x
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:25:32.684732+00:00
-- url     : https://prove2.me/submissions/c2db57e6-9827-46f1-ab4e-48e90cf7082f

-- Sol generated from Geometry/DiffusionSDE/FokkerPlanck.lean
import Mathlib
import Definitions.Def_Geometry_DiffusionSDE_FokkerPlanck
import Definitions.Def_Geometry_DiffusionSDE_OUProcess
/-
# Diffusion Models as SDEs — Part II: The Fokker–Planck Equation

This file derives the **Fokker–Planck (forward Kolmogorov) equation** for the
marginal densities of the Ornstein–Uhlenbeck forward process driving a
score-based diffusion model, and the stationary equation for its limit law.

For the OU SDE `dX = -θ X dt + σ dW` the marginal at time `t` is the Gaussian
`N(m(t), v(t))` with the moments from `OUProcess.lean`.  We write its density in
the (manifestly positive) exp-log form

  p(x,t) = exp( -½ log(2π v(t)) - (x - m(t))² / (2 v(t)) ),

which for `v(t) > 0` coincides with the usual `(2π v)^{-1/2} exp(-(x-m)²/(2v))`.

The Fokker–Planck operator for drift `f(x) = -θ x` and diffusion `σ²/2` is

  L p = -∂ₓ(f·p) + (σ²/2) ∂ₓₓ p = θ ∂ₓ(x·p) + (σ²/2) ∂ₓₓ p.

## Main results

* `gaussian_pos`              — the density is strictly positive.
* `hasDerivAt_gaussian_x`     — first spatial derivative `∂ₓ p = p·(-(x-m)/v)`.
* `hasDerivAt_gaussian_xx`    — second spatial derivative.
* `hasDerivAt_gaussian_t`     — time derivative via the moment chain rule.
* `ou_fokker_planck`          — **the OU marginal solves the Fokker–Planck PDE**.
* `stationary_fokker_planck`  — the stationary Gaussian `N(0, σ²/2θ)` is a
                                stationary solution (`L p_∞ = 0`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the time-dependent Gaussian with OU moments solves a
linear 2nd-order parabolic PDE; the stationary Gaussian kills the FP operator.
Experiment (Experimenter): compute ∂ₜ, ∂ₓ, ∂ₓₓ of the exp-log Gaussian via
`HasDerivAt`; the PDE then reduces to a *polynomial identity* in (x, m, v, θ, σ²)
discharged by `field_simp; ring` (after substituting the moment ODEs).
Analysis (Analyst): the exp-log parametrization is decisive — it turns the
normalization `(2πv)^{-1/2}` into an additive `-½log(2πv)` term whose
t-derivative is `-v'/(2v)`, so no `Real.sqrt` differentiation is needed and the
whole identity is rational.  The cancellation `-m(x-m) - ((x-m)²-v) = v - x(x-m)`
is the algebraic heart of the equation.
Critique (Critic): both PDEs are stated with genuine `deriv`s (not closed-form
placeholders); `ou_fokker_planck` needs `v(t)>0` and `θ≠0`; the stationary
identity is non-vacuous because `σ²/2θ` is the *exact* fixed point, not 0.
Synthesis (PI): the forward Kolmogorov layer; reused for time reversal.
-- !-- Lab Notes -- !--
-/


open Geometry.DiffusionSDE












open Geometry.DiffusionSDE in
theorem solution(m v x : ℝ) (hv : v ≠ 0) :
    HasDerivAt (fun y => gaussianDensity m v y)
      (gaussianDensity m v x * (-(x - m) / v)) x := by
  unfold gaussianDensity
  have hF : HasDerivAt (fun y : ℝ => -(Real.log (2 * Real.pi * v)) / 2 - (y - m) ^ 2 / (2 * v))
      (-(x - m) / v) x := by
    have h1 : HasDerivAt (fun y : ℝ => (y - m) ^ 2) (2 * (x - m)) x := by
      have := ((hasDerivAt_id x).sub_const m).pow 2; simpa using this
    have h3 := (h1.div_const (2 * v))
    have h4 := (hasDerivAt_const x (-(Real.log (2 * Real.pi * v)) / 2)).sub h3
    convert h4 using 1; field_simp; ring
  have hexp := hF.exp
  convert hexp using 1
