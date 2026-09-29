-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_inner_ibp_phase
-- name    : Zeta23.PrimeSide.inner_ibp_phase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:11:28.976053+00:00
-- url     : https://prove2.me/theorems/d2ae7e22-5f5b-43cb-beeb-e08d98f55248
-- title:
--   Integration by parts in $\tau'$ for the phase-shifted inner integral
-- statement:
--   Let $\Phi : \mathbb{R} \to \mathbb{R}$ be $C^1$, let $y \ne 0$, and let $\theta, \tau \in \mathbb{R}$ be an arbitrary phase and outer variable. The theorem is the exact integration-by-parts identity of Section 5.4 ("integrating by parts"), for the inner integral of the seam form against a phase-shifted cosine over $[T, 2T]$:
--   $$\int_T^{2T} \Phi(\tau - \tau')^2 \cos(\tau' y + \theta)\, d\tau' \;=\; \frac{\Phi(\tau - 2T)^2 \sin(2Ty + \theta) - \Phi(\tau - T)^2 \sin(Ty + \theta)}{y} \;+\; \frac{1}{y} \int_T^{2T} (\Phi^2)'(\tau - \tau')\, \sin(\tau' y + \theta)\, d\tau',$$
--   where $(\Phi^2)'$ denotes the derivative of $x \mapsto \Phi(x)^2$. Both sides are interval integrals; the identity is exact, with no hypotheses beyond smoothness and $y \ne 0$.
--
--   Taking absolute values (boundary terms $\le 2 \sup |\Phi^2|$-type contributions, and the derivative term of size $\int |(\Phi^2)'|$) yields the oscillatory gain of $1/|y|$; it is consumed by `abs_Mform_cos_phase_le`, the oscillatory bound driving the cross-term estimate $\mathcal{M}[\mu, P_X] \ll l\sqrt{X}$ of [prop:cross] (module `Zeta23.PrimeSideA.CrossMuPCore`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/CrossMuPCore.lean#L90-L122

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open MeasureTheory Real Set Finset
open scoped BigOperators
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.inner_ibp_phase (hΦ : ContDiff ℝ 1 Φ) {y : ℝ} (hy : y ≠ 0) (θ τ : ℝ) :
    ∫ τ' in T..(2 * T), Φ (τ - τ') ^ 2 * Real.cos (τ' * y + θ)
      = (Φ (τ - 2 * T) ^ 2 * Real.sin (2 * T * y + θ) - Φ (τ - T) ^ 2 * Real.sin (T * y + θ)) / y
        + y⁻¹ * ∫ τ' in T..(2 * T), deriv (fun x => Φ x ^ 2) (τ - τ') * Real.sin (τ' * y + θ) := by sorry
