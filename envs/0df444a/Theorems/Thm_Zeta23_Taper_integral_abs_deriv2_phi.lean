-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_abs_deriv2_phi
-- name    : Zeta23.Taper.integral_abs_deriv2_phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:36.589792+00:00
-- url     : https://prove2.me/theorems/8cdc7c33-7aba-4dc6-83f8-af801e31fa64
-- title:
--   The $L^1$ norm of $\varphi''$: $\|\varphi''\|_1 = 2\|\varrho''\|_1/w$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$.
--
--   Write $\|\varrho''\|_1 = \int_{\mathbb{R}} |\varrho''(x)|\,dx$ (`l1Deriv2`).
--
--   Assume $w > 0$ and $2w \le L$. Then
--
--   $$\int_{\mathbb{R}} \bigl|\varphi''(u)\bigr|\,du \;=\; \frac{2\,\|\varrho''\|_1}{w},$$
--
--   where $\varphi''$ is the iterated Lean derivative `deriv (deriv (phi ϱ L w))`. Each of the two ramps of $\varphi$ is a rescaled copy of $\varrho$ compressed to width $w$, so the second derivative picks up a factor $1/w^2$ over an interval of length $w$.
--
--   This is the identity $\|\varphi''\|_1 = 2\|\varrho''\|_1/w$ of [eq:phinorms]. It feeds the second-order decay bound `abs_phiHatR_mul_sq_le` for $\hat\varphi$, the bound `integral_abs_deriv2_phi_sq_le` for $(\varphi^2)''$, and the tail estimates in `Zeta23.Tail.eventually_tailPackage`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L340-L385, docstring tag [eq:phinorms]

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

theorem Zeta23.Taper.integral_abs_deriv2_phi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (deriv (phi ϱ L w)) u| = 2 * l1Deriv2 ϱ / w := by sorry
