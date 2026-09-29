-- Prove2me | Theorems.Thm_Zeta23_Taper_bConst_le_aConst
-- name    : Zeta23.Taper.bConst_le_aConst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:31:53.727664+00:00
-- url     : https://prove2.me/theorems/58a5a223-34bd-4e7f-b937-f10b2fe96519
-- title:
--   Comparison of the taper moments: $b \le a$
-- statement:
--   Throughout, $\varrho$ is a taper profile (`TaperProfile`): a monotone $C^3$ function $\mathbb{R}\to\mathbb{R}$ equal to $0$ on $(-\infty,0]$ and $1$ on $[1,\infty)$. For a window length $L$ and ramp width $w$, the taper is $\varphi(u) = \varrho\bigl((L/2 - |u|)/w\bigr)$: an even function with $0\le\varphi\le 1$, supported in $[-L/2,L/2]$ and equal to $1$ on $[-L/2+w,\,L/2-w]$.
--
--   The two normalized moments of the taper are $a = L^{-1}\int_{\mathbb{R}} \varphi(u)^2\,du$ (`aConst`) and $b = L^{-1}\int_{\mathbb{R}} \varphi(u)^4\,du$ (`bConst`), as in [eq:abdef].
--
--   Assume $w > 0$ and $2w \le L$. Then
--
--   $$b \le a,$$
--
--   which follows from $\varphi^4 \le \varphi^2$ (as $0 \le \varphi \le 1$) once both integrals are known to converge.
--
--   The ratio of $b$ to $a$ controls the main term of the mollified second moment; this comparison is used in `Zeta23.PrimeSide.localHyps_concrete`, `Zeta23.Tail.eventually_tailPackage`, `Zeta23.eventually_blockInputs`, and `Zeta23.eventually_side_conditions`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L527-L539

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

theorem Zeta23.Taper.bConst_le_aConst (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    bConst ϱ L w ≤ aConst ϱ L w := by sorry
