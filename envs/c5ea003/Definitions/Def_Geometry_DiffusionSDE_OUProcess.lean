-- Prove2me | Definitions.Def_Geometry_DiffusionSDE_OUProcess
-- name    : Geometry_DiffusionSDE_OUProcess
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:03:53.241638+00:00
-- url     : https://prove2.me/theorems/e4e61e02-fded-4592-ac90-7eb1e78803df
-- title:
--   Aether Catalog definitions — Geometry_DiffusionSDE_OUProcess
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.DiffusionSDE.OUProcess`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/DiffusionSDE/OUProcess.lean by skeleton subtraction
import Mathlib
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

namespace Geometry.DiffusionSDE

/-- Mean of the OU marginal at time `t`: `m(t) = m₀ e^{-θt}`. -/
noncomputable def ouMean (θ m0 t : ℝ) : ℝ := m0 * Real.exp (-θ * t)

/-- Stationary variance of the OU process: `v_∞ = σ²/(2θ)`. -/
noncomputable def stationaryVar (θ σ2 : ℝ) : ℝ := σ2 / (2 * θ)

/-- Variance of the OU marginal at time `t`:
`v(t) = v_∞ + (v₀ - v_∞) e^{-2θt}`. -/
noncomputable def ouVar (θ σ2 v0 t : ℝ) : ℝ :=
  stationaryVar θ σ2 + (v0 - stationaryVar θ σ2) * Real.exp (-(2 * θ) * t)







end Geometry.DiffusionSDE


