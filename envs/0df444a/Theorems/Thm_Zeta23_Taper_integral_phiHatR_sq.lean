-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_phiHatR_sq
-- name    : Zeta23.Taper.integral_phiHatR_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:34:40.740151+00:00
-- url     : https://prove2.me/theorems/b70b3f1c-6f0e-497e-8459-81daa10f0caa
-- title:
--   Plancherel for the taper: $\int \hat\varphi(r)^2\,dr = 2\pi a L$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$. The paper's Fourier transform is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`), and $\hat\varphi(r)$ denotes the real part of $h_\varphi$ at a real argument $r$ (`phiHatR`).
--
--   Let $a = L^{-1}\int \varphi^2$ (`aConst`).
--
--   Assume $w > 0$ and $2w \le L$. Then
--
--   $$\int_{\mathbb{R}} \hat\varphi(r)^2\,dr \;=\; 2\pi\, a\, L.$$
--
--   This is the Plancherel identity $\int \hat\varphi^2 = 2\pi \int \varphi^2 = 2\pi a L$ used in the $\mu$-part of [prop:trace]; it is obtained as the $y = 0$ case of the cosine inversion formula for $\hat\varphi^2$, using $A_\varphi(0) = \int \varphi^2 = aL$. It is consumed by `Zeta23.PrimeSide.localHyps_concrete`, where it fixes the total mass of the spectral weight in the mollified second-moment argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L459-L466, docstring tag [prop:trace]

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

theorem Zeta23.Taper.integral_phiHatR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ r, phiHatR ϱ L w r ^ 2 = 2 * π * aConst ϱ L w * L := by sorry
