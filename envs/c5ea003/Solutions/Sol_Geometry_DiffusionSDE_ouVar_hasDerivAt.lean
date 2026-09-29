-- Prove2me | solution 1 for Geometry.DiffusionSDE.ouVar_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:28:16.240395+00:00
-- url     : https://prove2.me/submissions/e8cca85a-f95a-433d-a96d-9ba72f65c23a

-- Sol generated from Geometry/DiffusionSDE/OUProcess.lean
import Mathlib
import Definitions.Def_Geometry_DiffusionSDE_OUProcess
/-
# Diffusion Models as SDEs — Part I: Ornstein–Uhlenbeck Marginal Moments

This file formalizes the deterministic *moment dynamics* of the Ornstein–Uhlenbeck
(OU) forward process used in score-based diffusion models.

The OU forward SDE is

  dX_t = -θ X_t dt + σ dW_t,    X_0 ∼ μ_0,

with θ > 0 (mean reversion) and σ² > 0 (diffusion).  Its marginal law `X_t` is
Gaussian for all `t`, completely described by its mean `m(t)` and variance `v(t)`.
Taking expectations of the SDE / its Itô square yields the closed *moment ODEs*

  m'(t) = -θ m(t),              (mean decay)
  v'(t) = -2θ v(t) + σ²,        (variance relaxation)

whose explicit solutions are

  m(t) = m₀ e^{-θt},
  v(t) = v_∞ + (v₀ - v_∞) e^{-2θt},     v_∞ = σ²/(2θ).

We prove (i) these explicit functions satisfy the moment ODEs (`HasDerivAt`),
and (ii) they converge as `t → ∞` to the **stationary distribution** moments
`m → 0`, `v → v_∞ = σ²/(2θ)`, i.e. `N(0, σ²/(2θ))`.

These are the scalar building blocks for the Fokker–Planck and reverse-time
results in the companion files.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the OU marginals are Gaussian with moments solving
linear ODEs whose unique fixed point is the stationary variance σ²/(2θ).
Experiment (Experimenter): encode m, v as explicit exponential solutions and
verify the ODEs via `HasDerivAt`; verify convergence via `Real.tendsto_exp_atBot`.
Analysis (Analyst): the variance ODE needs θ ≠ 0 to identify v_∞·2θ = σ²; the
mean ODE is unconditional. Convergence needs θ > 0 so that -θt, -2θt → -∞.
Critique (Critic): statements are non-vacuous (derivative values are exact, not
bounds); the limits are the genuine stationary moments, not 0 by accident.
Synthesis (PI): clean scalar OU layer reused downstream for Fokker–Planck.
-- !-- Lab Notes -- !--
-/


open Filter Topology
open scoped Topology

open Geometry.DiffusionSDE











open Geometry.DiffusionSDE in
theorem solution(θ σ2 v0 t : ℝ) (hθ : θ ≠ 0) :
    HasDerivAt (ouVar θ σ2 v0) (-(2 * θ) * ouVar θ σ2 v0 t + σ2) t := by
  unfold ouVar stationaryVar
  have h : HasDerivAt (fun t : ℝ => -(2 * θ) * t) (-(2 * θ)) t := by
    simpa using (hasDerivAt_id t).const_mul (-(2 * θ))
  have h2 := ((h.exp).const_mul (v0 - σ2 / (2 * θ))).const_add (σ2 / (2 * θ))
  convert h2 using 1
  field_simp
  ring
