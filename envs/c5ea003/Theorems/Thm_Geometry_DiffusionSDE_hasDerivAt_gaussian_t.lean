-- Prove2me | Theorems.Thm_Geometry_DiffusionSDE_hasDerivAt_gaussian_t
-- name    : Geometry.DiffusionSDE.hasDerivAt_gaussian_t
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:12:46.94537+00:00
-- url     : https://prove2.me/theorems/d4a9137d-5f17-43b5-a9dc-902ab68b9dd9
-- title:
--   Time derivative of a Gaussian with time-varying mean `mf` and variance `vf`
-- statement:
--   Time derivative of a Gaussian with time-varying mean `mf` and variance `vf`
--   (the two-parameter chain rule):
--   `∂ₜ p = p · ( (x-m)/v · m' + ((x-m)²-v)/(2v²) · v' )`.
--
--   ```lean
--   theorem Geometry.DiffusionSDE.hasDerivAt_gaussian_t(mf vf : ℝ → ℝ) (m' v' x t : ℝ)
--       (hv : 0 < vf t) (hm : HasDerivAt mf m' t) (hvd : HasDerivAt vf v' t) :
--       HasDerivAt (fun s => gaussianDensity (mf s) (vf s) x)
--         (gaussianDensity (mf t) (vf t) x *
--           ((x - mf t) / vf t * m' + ((x - mf t) ^ 2 - vf t) / (2 * (vf t) ^ 2) * v')) t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/DiffusionSDE/FokkerPlanck.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/DiffusionSDE/FokkerPlanck.lean#L102

-- Thm stub generated from Geometry/DiffusionSDE/FokkerPlanck.lean
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

theorem Geometry.DiffusionSDE.hasDerivAt_gaussian_t(mf vf : ℝ → ℝ) (m' v' x t : ℝ)
    (hv : 0 < vf t) (hm : HasDerivAt mf m' t) (hvd : HasDerivAt vf v' t) :
    HasDerivAt (fun s => gaussianDensity (mf s) (vf s) x)
      (gaussianDensity (mf t) (vf t) x *
        ((x - mf t) / vf t * m' + ((x - mf t) ^ 2 - vf t) / (2 * (vf t) ^ 2) * v')) t := by sorry
