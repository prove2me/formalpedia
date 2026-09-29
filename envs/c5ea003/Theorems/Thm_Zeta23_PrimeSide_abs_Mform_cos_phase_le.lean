-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_Mform_cos_phase_le
-- name    : Zeta23.PrimeSide.abs_Mform_cos_phase_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:11:44.116766+00:00
-- url     : https://prove2.me/theorems/d7d99dfb-d943-4108-ad4c-75b02fa16480
-- title:
--   Oscillatory bound: $|\mathcal{M}[u, \cos(\cdot\, y + \theta)]| \le (4B + DT)\bigl(\int \Phi^2\bigr)/|y|$
-- statement:
--   For a weight $\Phi : \mathbb{R} \to \mathbb{R}$ and a height $T$, the bilinear seam form of Section 5.4 is
--   $$\mathcal{M}[u_1, u_2] \;=\; \iint_{I \times I} \Phi(\tau - \tau')^2\, u_1(\tau)\, u_2(\tau')\, d\tau\, d\tau', \qquad I = [T, 2T].$$
--   Assume $T \ge 0$; $\Phi$ is $C^1$ with $\Phi^2$ integrable; $u$ is $C^1$ with $|u| \le B$ and $|u'| \le D$ on $I$; $y \ne 0$; and $\theta \in \mathbb{R}$ is an arbitrary phase. The theorem is the oscillatory bound of Section 5.4 (the paper's $|\int_I m(\tau')\cos(\tau' y)\,d\tau'| \le (2\sup|m| + \int_I |m'|)/y$), in explicit phase-shifted form:
--   $$\bigl|\mathcal{M}[u,\; \cos(\cdot\, y + \theta)]\bigr| \;\le\; \frac{(4B + D\,T)\,\int_{\mathbb{R}} \Phi(x)^2\, dx}{|y|}.$$
--   The proof integrates by parts in $\tau'$ (`inner_ibp_phase`). Including the free phase $\theta$ covers $\sin$ (at $\theta = -\pi/2$) and, more generally, complex coefficients via $\mathrm{Re}(c\, e^{-i\tau y}) = \|c\| \cos(\tau y - \arg c)$, as needed for the character prime sums of Theorem E; the unshifted case $\theta = 0$ is the companion lemma `abs_Mform_cos_le`.
--
--   In the project it is the engine behind `prop_cross_muP`, the cross-term bound $\mathcal{M}[\mu, P_X] \ll l\sqrt{X}$ of [prop:cross] (module `Zeta23.PrimeSideA.CrossMuPCore`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/CrossMuPCore.lean#L124-L266

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
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.abs_Mform_cos_phase_le (hT : 0 ≤ T) (hΦ : ContDiff ℝ 1 Φ)
    (hΦint : Integrable (fun x => Φ x ^ 2)) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {B D : ℝ}
    (hB : ∀ τ ∈ Set.Icc T (2 * T), |u τ| ≤ B) (hD : ∀ τ ∈ Set.Icc T (2 * T), |deriv u τ| ≤ D)
    {y : ℝ} (hy : y ≠ 0) (θ : ℝ) :
    |Mform Φ T u (fun t => Real.cos (t * y + θ))| ≤ (4 * B + D * T) * (∫ x, Φ x ^ 2) / |y| := by sorry
