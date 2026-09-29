-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_PhiR_sq_mul_cos
-- name    : Zeta23.Taper.integral_PhiR_sq_mul_cos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:34:19.677649+00:00
-- url     : https://prove2.me/theorems/0ad0967e-7627-472d-8e9b-a8a9399f8d30
-- title:
--   Fourier inversion for $\Phi^2$: $\int \Phi(x)^2 \cos(xy)\,dx = 2\pi\,g(y)$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$.
--
--   Let $\Phi$ be the paper Fourier transform of $\varphi^2$ at real arguments (`PhiR`), and let $g = \varphi^2 \star \varphi^2$ be the autocorrelation $g(y) = \int \varphi(u)^2 \varphi(u+y)^2\,du$, as in [eq:PhigA].
--
--   Assume $w > 0$ and $2w \le L$. Then for every real $y$,
--
--   $$\int_{\mathbb{R}} \Phi(x)^2 \cos(xy)\,dx \;=\; 2\pi\, g(y).$$
--
--   This is [eq:Phi2FT] ($\int \Phi^2 e^{ixy} dx = 2\pi g(y)$) in cosine form: $\Phi^2$ is even and real, so the sine part vanishes. Since $\Phi^2 = \hat g$ up to the paper's conventions, this is Fourier inversion for the autocorrelation of $\varphi^2$; it is consumed by `Zeta23.PrimeSide.localHyps_concrete` on the prime side of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L447-L457, docstring tag [eq:Phi2FT]

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
open scoped FourierTransform ComplexConjugate
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.integral_PhiR_sq_mul_cos (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (y : ℝ) : ∫ x, PhiR ϱ L w x ^ 2 * Real.cos (x * y) = 2 * π * g ϱ L w y := by sorry
