-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_phiHatR_sq_mul_sq_le
-- name    : Zeta23.Taper.integral_phiHatR_sq_mul_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:12.362162+00:00
-- url     : https://prove2.me/theorems/d763a351-d4b9-4659-93f1-451906fe37e4
-- title:
--   Weighted second moment of $\hat\varphi$: $\int \hat\varphi(r)^2\, r^2\,dr \le 8 + 2(c_\varrho/w)^2$
-- statement:
--   Fix a taper profile $\varrho$ (a nondecreasing $C^3$ function on $\mathbb{R}$ vanishing on $(-\infty,0]$ and equal to $1$ on $[1,\infty)$), a ramp width $w$ and a support length $L$, and let $\varphi(u) := \varrho\big((L/2-|u|)/w\big)$ be the taper of [eq:phidef]. Write $\hat\varphi(r)$ for the (real-valued) restriction to $\mathbb{R}$ of the paper Fourier transform $h_\varphi(z) = \int_{\mathbb{R}} \varphi(u)\,e^{izu}\,du$, and let $c_\varrho := 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$ be the profile constant of [eq:phinorms].
--
--   Assuming $1 \le w$ and $8w \le L$, the theorem asserts
--   $$\int_{\mathbb{R}} \hat\varphi(r)^2\, r^2 \, dr \;\le\; 8 + 2\left(\frac{c_\varrho}{w}\right)^2.$$
--   The proof combines the pointwise bounds behind [eq:psidef]: $\hat\varphi(r)^2 r^2 \le 4$ on $|r| \le 1$ and $\hat\varphi(r)^2 r^2 \le (c_\varrho/w)^2 r^{-2}$ on $|r| > 1$.
--
--   In the project this is one of the concrete taper integrals fed into `Zeta23.PrimeSide.localHyps_concrete`, which verifies the local analytic hypotheses used on the prime side of the mollified second-moment argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L972-L980, docstring tag [eq:psidef]

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

theorem Zeta23.Taper.integral_phiHatR_sq_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, phiHatR ϱ L w r ^ 2 * r ^ 2 ≤ 8 + 2 * (cRho ϱ / w) ^ 2 := by sorry
