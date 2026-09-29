-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_phiHatR_sq_mul_cos
-- name    : Zeta23.Taper.integral_phiHatR_sq_mul_cos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:34:35.410972+00:00
-- url     : https://prove2.me/theorems/d5be5e6d-91c7-4bf0-8daa-9e5c0eeb22bb
-- title:
--   Fourier inversion for $\hat\varphi^2$: $\int \hat\varphi(r)^2 \cos(ry)\,dr = 2\pi A_\varphi(y)$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$. The paper's Fourier transform is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`), and $\hat\varphi(r)$ denotes the real part of $h_\varphi$ at a real argument $r$ (`phiHatR`).
--
--   Let $A_\varphi = \varphi \star \varphi$ be the autocorrelation $A_\varphi(y) = \int \varphi(u)\,\varphi(u+y)\,du$, as in [eq:PhigA].
--
--   Assume $w > 0$ and $2w \le L$. Then for every real $y$,
--
--   $$\int_{\mathbb{R}} \hat\varphi(r)^2 \cos(r y)\,dr \;=\; 2\pi\, A_\varphi(y).$$
--
--   Since $\hat\varphi^2 = (A_\varphi)^{\wedge}$ in the paper's convention, this is Fourier inversion in cosine form; it is the identity used in the P-part of [prop:trace] ($\int \hat\varphi(\tau - \tau_k)^2 \cos(\tau y)\,d\tau = 2\pi A_\varphi(y)\cos(\tau_k y)$). It is consumed by `Zeta23.PrimeSide.localHyps_concrete` and, at $y = 0$, yields the Plancherel identity `Zeta23.Taper.integral_phiHatR_sq`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L437-L445, docstring tag [prop:trace]

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

theorem Zeta23.Taper.integral_phiHatR_sq_mul_cos (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (y : ℝ) : ∫ r, phiHatR ϱ L w r ^ 2 * Real.cos (r * y) = 2 * π * Aphi ϱ L w y := by sorry
