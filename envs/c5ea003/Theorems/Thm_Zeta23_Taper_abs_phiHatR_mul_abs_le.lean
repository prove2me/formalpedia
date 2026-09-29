-- Prove2me | Theorems.Thm_Zeta23_Taper_abs_phiHatR_mul_abs_le
-- name    : Zeta23.Taper.abs_phiHatR_mul_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:31:25.792659+00:00
-- url     : https://prove2.me/theorems/a53dee60-72d6-4c2e-8919-937e37d9bc08
-- title:
--   First-order decay of the taper transform: $|\hat\varphi(r)|\,|r| \le 2$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$. The paper's Fourier transform is $h_f(z) = \int_{\mathbb{R}} f(u)\,e^{izu}\,du$ (`paperFT`), and $\hat\varphi(r)$ denotes the real part of $h_\varphi$ at a real argument $r$ (`phiHatR`).
--
--   Assume $w > 0$ and $2w \le L$. Then for every real $r$,
--
--   $$|\hat\varphi(r)|\,|r| \le 2.$$
--
--   The bound comes from one integration by parts together with the norm identity $\|\varphi'\|_1 = 2$. It is one of the three decay estimates feeding the envelope bound $|\hat\varphi| \le \psi$; it is used in `Zeta23.PrimeSide.localHyps_concrete` (the concrete local hypotheses on the prime side) and in the second-moment estimate `Zeta23.Taper.integral_phiHatR_sq_mul_sq_le`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L305-L314

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

theorem Zeta23.Taper.abs_phiHatR_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |phiHatR ϱ L w r| * |r| ≤ 2 := by sorry
