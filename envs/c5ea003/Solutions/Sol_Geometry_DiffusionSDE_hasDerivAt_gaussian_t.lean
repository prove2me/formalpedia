-- Prove2me | solution 1 for Geometry.DiffusionSDE.hasDerivAt_gaussian_t
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:25:32.181357+00:00
-- url     : https://prove2.me/submissions/44e31490-ec63-4cab-9bbd-02dd0269a1f4

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
theorem solution(mf vf : ℝ → ℝ) (m' v' x t : ℝ)
    (hv : 0 < vf t) (hm : HasDerivAt mf m' t) (hvd : HasDerivAt vf v' t) :
    HasDerivAt (fun s => gaussianDensity (mf s) (vf s) x)
      (gaussianDensity (mf t) (vf t) x *
        ((x - mf t) / vf t * m' + ((x - mf t) ^ 2 - vf t) / (2 * (vf t) ^ 2) * v')) t := by
  unfold gaussianDensity
  have hvne : vf t ≠ 0 := ne_of_gt hv
  have hw : HasDerivAt (fun s => 2 * Real.pi * vf s) (2 * Real.pi * v') t :=
    hvd.const_mul (2 * Real.pi)
  have hwne : 2 * Real.pi * vf t ≠ 0 := by positivity
  have hlog := hw.log hwne
  have hA : HasDerivAt (fun s => -(Real.log (2 * Real.pi * vf s)) / 2)
      (-((2 * Real.pi * v') / (2 * Real.pi * vf t)) / 2) t := (hlog.neg).div_const 2
  have hxm : HasDerivAt (fun s => x - mf s) (-m') t := by
    simpa using (hasDerivAt_const t x).sub hm
  have hxm2 : HasDerivAt (fun s => (x - mf s) ^ 2) (2 * (x - mf t) * (-m')) t := by
    simpa using hxm.pow 2
  have hden : HasDerivAt (fun s => 2 * vf s) (2 * v') t := hvd.const_mul 2
  have hdenne : 2 * vf t ≠ 0 := by positivity
  have hB : HasDerivAt (fun s => (x - mf s) ^ 2 / (2 * vf s))
      ((2 * (x - mf t) * (-m') * (2 * vf t) - (x - mf t) ^ 2 * (2 * v')) / (2 * vf t) ^ 2) t :=
    hxm2.div hden hdenne
  have hexp := (hA.sub hB).exp
  convert hexp using 2; field_simp; ring
