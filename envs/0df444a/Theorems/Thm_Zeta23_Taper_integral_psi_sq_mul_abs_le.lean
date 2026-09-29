-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_psi_sq_mul_abs_le
-- name    : Zeta23.Taper.integral_psi_sq_mul_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:43.728369+00:00
-- url     : https://prove2.me/theorems/85765349-52ba-48dc-9f3b-38fb9b45edeb
-- title:
--   Third $\psi$-integral of [eq:psiints]: $\int_{\mathbb{R}} \psi(r)^2 |r|\,dr \le 8 + 8\log\!\big(c_\varrho L/(4w)\big)$
-- statement:
--   Let $\varrho$ be a taper profile with constant $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$, and let $\psi(r) := \min\big(L,\ 2/|r|,\ c_\varrho/(w r^2)\big)$ (with $\psi(0) = L$) be the decay majorant of [eq:psidef], for support length $L$ and ramp width $w$.
--
--   Assuming $1 \le w$ and $8w \le L$, the theorem asserts
--   $$\int_{\mathbb{R}} \psi(r)^2\,|r|\,dr \;\le\; 8 + 8\log\!\left(\frac{c_\varrho L}{4w}\right).$$
--   The paper records this with an asymptotic "$=$"; the formal statement is the inequality. The proof splits $(0,\infty)$ at $2/L$ and $c_\varrho/(2w)$ and bounds $\int_0^\infty \psi^2 r$ by $L^2(2/L)^2/2 + 4\log(c_\varrho L/4w) + 2$, using the appropriate entry of the minimum on each range.
--
--   In the project this moment is consumed by `Zeta23.PrimeSide.localHyps_concrete`, which packages the concrete taper integrals needed for the prime-side (mollified second moment) estimates.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L675-L780, docstring tag [eq:psiints]

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

theorem Zeta23.Taper.integral_psi_sq_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, psi ϱ L w r ^ 2 * |r| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) := by sorry
