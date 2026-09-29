-- Prove2me | solution 1 for Geometry.DiffusionSDE.ou_fokker_planck
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:30:58.307914+00:00
-- url     : https://prove2.me/submissions/a6acb521-51cd-4a8a-8ec1-be1a414c6812

-- Sol generated from Geometry/DiffusionSDE/FokkerPlanck.lean
import Mathlib
import Definitions.Def_Geometry_DiffusionSDE_FokkerPlanck
import Definitions.Def_Geometry_DiffusionSDE_OUProcess
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_t
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_x
import Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_xx
import Theorems.Thm_Geometry_DiffusionSDE_ouMean_hasDerivAt
import Theorems.Thm_Geometry_DiffusionSDE_ouVar_hasDerivAt
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
theorem solution(θ σ2 m0 v0 x t : ℝ) (hθ : θ ≠ 0)
    (hv : 0 < ouVar θ σ2 v0 t) :
    deriv (fun s => ouDensity θ σ2 m0 v0 x s) t
      = θ * deriv (fun y => y * ouDensity θ σ2 m0 v0 y t) x
        + (σ2 / 2) * deriv (fun y => deriv (fun z => ouDensity θ σ2 m0 v0 z t) y) x := by
  set m := ouMean θ m0 with hm_def
  set v := ouVar θ σ2 v0 with hv_def
  have hvne : v t ≠ 0 := ne_of_gt hv
  have ht : HasDerivAt (fun s => ouDensity θ σ2 m0 v0 x s)
      (gaussianDensity (m t) (v t) x *
        ((x - m t) / v t * (-θ * m t)
          + ((x - m t) ^ 2 - v t) / (2 * (v t) ^ 2) * (-(2 * θ) * v t + σ2))) t :=
    hasDerivAt_gaussian_t m v (-θ * m t) (-(2 * θ) * v t + σ2) x t hv
      (ouMean_hasDerivAt θ m0 t) (ouVar_hasDerivAt θ σ2 v0 t hθ)
  rw [ht.deriv]
  have hxp : HasDerivAt (fun y => y * ouDensity θ σ2 m0 v0 y t)
      (1 * gaussianDensity (m t) (v t) x
        + x * (gaussianDensity (m t) (v t) x * (-(x - m t) / v t))) x := by
    have := (hasDerivAt_id x).mul (hasDerivAt_gaussian_x (m t) (v t) x hvne)
    simpa [ouDensity] using this
  rw [hxp.deriv]
  have hinner : (fun y => deriv (fun z => ouDensity θ σ2 m0 v0 z t) y)
      = (fun y => gaussianDx (m t) (v t) y) := by
    funext y
    have := (hasDerivAt_gaussian_x (m t) (v t) y hvne).deriv
    simpa [ouDensity, gaussianDx] using this
  rw [hinner, (hasDerivAt_gaussian_xx (m t) (v t) x hvne).deriv]
  field_simp
  ring
