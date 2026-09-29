-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_abs_deriv_phi
-- name    : Zeta23.Taper.integral_abs_deriv_phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:42.8833+00:00
-- url     : https://prove2.me/theorems/2beeb5da-a4ed-4113-9e6f-4da470c275b3
-- title:
--   The $L^1$ norm of $\varphi'$: $\|\varphi'\|_1 = 2$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$.
--
--   Assume $w > 0$ and $2w \le L$. Then
--
--   $$\int_{\mathbb{R}} \bigl|\varphi'(u)\bigr|\,du \;=\; 2,$$
--
--   where $\varphi'$ is the Lean derivative `deriv (phi ϱ L w)`. Indeed $\varphi$ rises monotonically from $0$ to $1$ across the left ramp and falls back across the right ramp, so the total variation is exactly $2$, independently of $L$ and $w$.
--
--   This is the identity $\|\varphi'\|_1 = 2$ of [eq:phinorms]. It yields the first-order decay bound `abs_phiHatR_mul_abs_le` for $\hat\varphi$ and enters the bound `integral_abs_deriv2_phi_sq_le` on $\|(\varphi^2)''\|_1$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L127-L137, docstring tag [eq:phinorms]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
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

theorem Zeta23.Taper.integral_abs_deriv_phi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (phi ϱ L w) u| = 2 := by sorry
