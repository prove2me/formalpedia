-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_abs_deriv_phi_sq
-- name    : Zeta23.Taper.integral_abs_deriv_phi_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:10.499573+00:00
-- url     : https://prove2.me/theorems/dd788b16-d2d3-4d44-8db8-93d6c3754cb6
-- title:
--   The $L^1$ norm of $(\varphi^2)'$: $\|(\varphi^2)'\|_1 = 2$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$.
--
--   Assume $w > 0$ and $2w \le L$. Then
--
--   $$\int_{\mathbb{R}} \bigl|(\varphi^2)'(u)\bigr|\,du \;=\; 2,$$
--
--   where $(\varphi^2)'$ is the Lean derivative of $u \mapsto \varphi(u)^2$. As with $\varphi$ itself, $\varphi^2$ climbs monotonically from $0$ to $1$ and back, so its total variation is exactly $2$.
--
--   This is the identity $\|(\varphi^2)'\|_1 = 2$ of [eq:phinorms]; it yields the first-order decay bound `Zeta23.Taper.abs_PhiR_mul_abs_le` for the transform $\Phi$ of $\varphi^2$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L139-L164, docstring tag [eq:phinorms]

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

theorem Zeta23.Taper.integral_abs_deriv_phi_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (fun u => phi ϱ L w u ^ 2) u| = 2 := by sorry
