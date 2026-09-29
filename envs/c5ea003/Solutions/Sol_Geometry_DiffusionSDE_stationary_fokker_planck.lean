-- Prove2me | solution 1 for Geometry.DiffusionSDE.stationary_fokker_planck
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:30:59.339662+00:00
-- url     : https://prove2.me/submissions/68c799e2-1851-414f-842a-150828f0f5db

-- Sol generated from Geometry/DiffusionSDE/FokkerPlanck.lean
import Mathlib
import Definitions.Def_Geometry_DiffusionSDE_FokkerPlanck
import Definitions.Def_Geometry_DiffusionSDE_OUProcess
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_x
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_xx
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
theorem solution(θ σ2 x : ℝ) (hθ : 0 < θ) (hσ : 0 < σ2) :
    θ * deriv (fun y => y * gaussianDensity 0 (stationaryVar θ σ2) y) x
      + (σ2 / 2) * deriv (fun y => deriv (fun z => gaussianDensity 0 (stationaryVar θ σ2) z) y) x
      = 0 := by
  have hv : (0 : ℝ) < stationaryVar θ σ2 := by unfold stationaryVar; positivity
  have hvne : stationaryVar θ σ2 ≠ 0 := ne_of_gt hv
  have hxp : HasDerivAt (fun y => y * gaussianDensity 0 (stationaryVar θ σ2) y)
      (1 * gaussianDensity 0 (stationaryVar θ σ2) x
        + x * (gaussianDensity 0 (stationaryVar θ σ2) x * (-(x - 0) / stationaryVar θ σ2))) x := by
    have := (hasDerivAt_id x).mul (hasDerivAt_gaussian_x 0 (stationaryVar θ σ2) x hvne)
    simpa using this
  rw [hxp.deriv]
  have hinner : (fun y => deriv (fun z => gaussianDensity 0 (stationaryVar θ σ2) z) y)
      = (fun y => gaussianDx 0 (stationaryVar θ σ2) y) := by
    funext y
    have := (hasDerivAt_gaussian_x 0 (stationaryVar θ σ2) y hvne).deriv
    simpa [gaussianDx] using this
  rw [hinner, (hasDerivAt_gaussian_xx 0 (stationaryVar θ σ2) x hvne).deriv]
  unfold stationaryVar
  field_simp
  ring
