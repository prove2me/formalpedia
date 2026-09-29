-- Prove2me | Theorems.Thm_Zeta23_Taper_g_le_Aphi
-- name    : Zeta23.Taper.g_le_Aphi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:32:48.360962+00:00
-- url     : https://prove2.me/theorems/4f0f641a-0b56-4456-b45e-aef7f6db7c24
-- title:
--   Pointwise comparison of autocorrelations: $g \le A_\varphi$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$.
--
--   With the autocorrelation $(v \star v)(y) = \int_{\mathbb{R}} v(u)\,v(u+y)\,du$, set $g = \varphi^2 \star \varphi^2$ and $A_\varphi = \varphi \star \varphi$, as in [eq:PhigA].
--
--   Assume $w > 0$ and $2w \le L$. Then for every real $y$,
--
--   $$g(y) \le A_\varphi(y),$$
--
--   since $0 \le \varphi \le 1$ gives $\varphi(u)^2\varphi(u+y)^2 \le \varphi(u)\varphi(u+y)$ pointwise.
--
--   The functions $g$ and $A_\varphi$ are (up to constants) the inverse Fourier transforms of $\Phi^2$ and $\hat\varphi^2$; this comparison is consumed by `Zeta23.PrimeSide.localHyps_concrete` in the prime-side estimates of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L182-L190

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

theorem Zeta23.Taper.g_le_Aphi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    g ϱ L w y ≤ Aphi ϱ L w y := by sorry
