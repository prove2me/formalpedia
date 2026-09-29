-- Prove2me | Theorems.Thm_Zeta23_Taper_hasSum_phiHatR_sq
-- name    : Zeta23.Taper.hasSum_phiHatR_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:47:48.824809+00:00
-- url     : https://prove2.me/theorems/7a216e0f-15a3-423a-9fb3-57a886ac570a
-- title:
--   Poisson summation for squares: $\sum_k \hat\varphi(\gamma - \tau_k)^2 = a L^2$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$. The paper's Fourier transform is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`), and $\hat\varphi(r)$ denotes the real part of $h_\varphi$ at a real argument $r$ (`phiHatR`).
--
--   Let $a = L^{-1}\int \varphi^2$ (`aConst`), and for a base point $T$ let $\tau_k = T + k \cdot 2\pi/L$ ($k \in \mathbb{Z}$).
--
--   Assume $w > 0$ and $2w \le L$. Then for every real $\gamma$, the series converges (unconditional `HasSum` over $k \in \mathbb{Z}$) with
--
--   $$\sum_{k \in \mathbb{Z}} \hat\varphi(\gamma - \tau_k)^2 \;=\; a\,L^2.$$
--
--   This is the \"in particular\" clause of [lem:poisson], obtained from the general product form at $\tau = \tau' = \gamma$ using $\Phi(0) = aL$. Crucially the value is independent of $\gamma$: every zero ordinate receives the same total sampling weight, which is what `Zeta23.eventually_blockInputs` uses to normalize the block decomposition of the second-moment argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Poisson.lean#L366-L373, docstring tag [lem:poisson]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.hasSum_phiHatR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (T γ : ℝ) :
    HasSum (fun k : ℤ => phiHatR ϱ L w (γ - (T + k * (2 * π / L))) ^ 2)
      (aConst ϱ L w * L ^ 2) := by sorry
