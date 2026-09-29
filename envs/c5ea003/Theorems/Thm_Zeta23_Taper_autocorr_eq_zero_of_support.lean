-- Prove2me | Theorems.Thm_Zeta23_Taper_autocorr_eq_zero_of_support
-- name    : Zeta23.Taper.autocorr_eq_zero_of_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:47:29.756848+00:00
-- url     : https://prove2.me/theorems/af2ca5c3-ad36-432f-ab09-d28aa05e4b07
-- title:
--   Support of the autocorrelation: $(v \star v)(y) = 0$ for $|y| \ge 2M$
-- statement:
--   For $v : \mathbb{R} \to \mathbb{R}$, the autocorrelation is $(v \star v)(y) = \int_{\mathbb{R}} v(u)\,v(u+y)\,du$ (`Params.autocorr`).
--
--   Suppose $v$ vanishes off $(-M, M)$, i.e. $v(u) = 0$ whenever $|u| \ge M$. Then for every real $y$ with $2M \le |y|$,
--
--   $$(v \star v)(y) = 0,$$
--
--   since the supports of $v$ and of its translate $v(\cdot + y)$ are disjoint for such shifts.
--
--   This is a supporting lemma in the `Zeta23.Taper.Decay` module for the compactly supported autocorrelations $A_\varphi = \varphi \star \varphi$ and $g = \varphi^2 \star \varphi^2$ of the taper, which appear in the prime-side analysis of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L105-L118

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

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.autocorr_eq_zero_of_support (v : ℝ → ℝ) {M : ℝ} (hz : ∀ u, M ≤ |u| → v u = 0) {y : ℝ}
    (hy : 2 * M ≤ |y|) : Params.autocorr v y = 0 := by sorry
