-- Prove2me | Theorems.Thm_Zeta23_Taper_integrable_phi_mul_shift
-- name    : Zeta23.Taper.integrable_phi_mul_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:32:43.526543+00:00
-- url     : https://prove2.me/theorems/bb3bae1e-ac28-4653-b0c8-326d6880e95f
-- title:
--   Integrability of $u \mapsto \varphi(u)\,\varphi(u+y)$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$.
--
--   Assume $w > 0$ and $2w \le L$. Then for every real shift $y$, the function
--
--   $$u \;\longmapsto\; \varphi(u)\,\varphi(u + y)$$
--
--   is integrable on $\mathbb{R}$ (it is continuous with compact support).
--
--   This provides the integrand of the autocorrelation $A_\varphi = \varphi \star \varphi$ with a well-defined integral; it is consumed by `Zeta23.Taper.g_le_Aphi`, the comparison $g \le A_\varphi$ used on the prime side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L144-L153

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

theorem Zeta23.Taper.integrable_phi_mul_shift (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    Integrable fun u => phi ϱ L w u * phi ϱ L w (u + y) := by sorry
