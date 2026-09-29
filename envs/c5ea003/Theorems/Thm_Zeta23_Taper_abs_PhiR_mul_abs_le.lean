-- Prove2me | Theorems.Thm_Zeta23_Taper_abs_PhiR_mul_abs_le
-- name    : Zeta23.Taper.abs_PhiR_mul_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:16.566892+00:00
-- url     : https://prove2.me/theorems/4f455777-a0d1-4e27-97bb-ce0d0071d261
-- title:
--   First-order decay: $|\Phi(r)|\,|r| \le 2$
-- statement:
--   **Setup.** As in the companion bounds, $\varrho$ is a taper profile, $\varphi(u) = \varrho\bigl((L/2-|u|)/w\bigr)$ the taper with $0 < w$ and $2w \le L$, and `PhiR ϱ L w r` $= \operatorname{Re}\Phi(r)$ is the real-line value of $\Phi = \widehat{\varphi^2}$, the paper Fourier transform $\Phi(z) = \int\varphi(u)^2 e^{izu}\,du$.
--
--   **Statement.** For every real $r$,
--   $$|\Phi(r)|\cdot |r| \;\le\; 2.$$
--   This is the standard one-integration-by-parts decay: $|\Phi(r)|\,|r| \le \int |(\varphi^2)'| = 2$, since $\varphi^2$ increases from $0$ to at most $1$ and back, giving total variation at most $2$.
--
--   **Role.** The middle of the three bounds forming the envelope $\psi$ of [eq:psidef] for $\Phi$ on the real line (with `abs_PhiR_le_L` and `abs_PhiR_mul_sq_le`). It is consumed by `Zeta23.PrimeSide.localHyps_concrete` and by `Zeta23.Taper.integral_PhiR_sq_mul_sq_le` (the $\psi$-integral bounds [eq:psiints] used in the second-moment computation).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L342-L351

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.abs_PhiR_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| * |r| ≤ 2 := by sorry
