-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_PhiR_sq_mul_sq_le
-- name    : Zeta23.Taper.integral_PhiR_sq_mul_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:34:25.596646+00:00
-- url     : https://prove2.me/theorems/a46bb8f3-d316-4dc7-9d54-e3b36c0c9043
-- title:
--   Second moment bound: $\int \Phi(x)^2 x^2\,dx \le 8 + 2(c_\varrho/w)^2$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$. The profile constant is $c_\varrho = 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$ (`cRho`).
--
--   Let $\Phi$ be the paper Fourier transform of $\varphi^2$ at real arguments (`PhiR`).
--
--   Assume $w \ge 1$ and $8w \le L$. Then
--
--   $$\int_{\mathbb{R}} \Phi(x)^2\, x^2 \,dx \;\le\; 8 + 2\left(\frac{c_\varrho}{w}\right)^2.$$
--
--   The proof follows the same route (via the envelope $\psi$) as the corresponding bound for $\hat\varphi$: the decay estimates $|\Phi(x)|\,|x| \le 2$ and $|\Phi(x)|\,x^2 \le c_\varrho/w$ dominate $\Phi(x)^2 x^2$ pointwise by a function that integrates to the stated constant. It is consumed by `Zeta23.PrimeSide.localHyps_concrete`, where a finite second moment of $\Phi$ is one of the concrete local hypotheses on the prime side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L991-L998

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

theorem Zeta23.Taper.integral_PhiR_sq_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ x, PhiR ϱ L w x ^ 2 * x ^ 2 ≤ 8 + 2 * (cRho ϱ / w) ^ 2 := by sorry
