-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_psi_sq_le
-- name    : Zeta23.Taper.integral_psi_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:36.904688+00:00
-- url     : https://prove2.me/theorems/cde85c44-a944-4d3c-b00b-8d3cca7b9295
-- title:
--   Second $\psi$-integral of [eq:psiints]: $\int_{\mathbb{R}} \psi^2 \le 8L$
-- statement:
--   Let $\varrho$ be a taper profile with constant $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$, and let $\psi(r) := \min\big(L,\ 2/|r|,\ c_\varrho/(w r^2)\big)$ (with $\psi(0) = L$) be the decay majorant of [eq:psidef] for support length $L$ and ramp width $w$.
--
--   Assuming $1 \le w$ and $8w \le L$, the theorem asserts
--   $$\int_{\mathbb{R}} \psi(r)^2\,dr \;\le\; 8L.$$
--   The proof uses only the two-term bound $\psi \le \min(L,\ 2/|r|)$: by evenness, $\int_{\mathbb{R}} = 2\int_0^\infty \le 2\big(\int_0^{2/L} L^2 + \int_{2/L}^{\infty} 4 r^{-2}\big) = 2(2L + 2L)$.
--
--   In the project this is one of the $\psi$-moments of [eq:psiints] consumed by `Zeta23.PrimeSide.localHyps_concrete` when verifying the concrete local hypotheses on the prime side of the second-moment computation.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L782-L845, docstring tag [eq:psiints]

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

theorem Zeta23.Taper.integral_psi_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, psi ϱ L w r ^ 2 ≤ 8 * L := by sorry
