-- Prove2me | Theorems.Thm_Zeta23_Taper_integral_abs_deriv2_phi_sq_le
-- name    : Zeta23.Taper.integral_abs_deriv2_phi_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:30:52.227977+00:00
-- url     : https://prove2.me/theorems/f23d3377-383b-42e3-8e0a-97efac4f6819
-- title:
--   The $L^1$ norm of $(\varphi^2)''$ is at most $c_\varrho/w$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$. The profile constant is $c_\varrho = 4\|\varrho'\|_\infty + 4\|\varrho''\|_1$ (`cRho`).
--
--   Assume $w \ge 1$ and $2w \le L$. Then
--
--   $$\int_{\mathbb{R}} \bigl|(\varphi^2)''(u)\bigr|\,du \;\le\; \frac{c_\varrho}{w},$$
--
--   where $(\varphi^2)''$ is the iterated Lean derivative of $u \mapsto \varphi(u)^2$. Expanding $(\varphi^2)'' = 2(\varphi')^2 + 2\varphi\varphi''$ and using $\|\varphi'\|_1 = 2$, $\|\varphi'\|_\infty = \|\varrho'\|_\infty/w$, $0 \le \varphi \le 1$ and $\|\varphi''\|_1 = 2\|\varrho''\|_1/w$ gives the bound; the hypothesis $w \ge 1$ is used to absorb the $1/w^2$ term.
--
--   This is the estimate $\|(\varphi^2)''\|_1 \le c_\varrho/w$ of [eq:phinorms]; it feeds the second-order decay bound `Zeta23.Taper.abs_PhiR_mul_sq_le` for the transform $\Phi$ of $\varphi^2$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L387-L475, docstring tag [eq:phinorms]

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

theorem Zeta23.Taper.integral_abs_deriv2_phi_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (deriv (fun u => phi ϱ L w u ^ 2)) u| ≤ cRho ϱ / w := by sorry
