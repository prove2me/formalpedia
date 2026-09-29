-- Prove2me | Theorems.Thm_Zeta23_Taper_autocorr_le_of_support
-- name    : Zeta23.Taper.autocorr_le_of_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:31:48.082489+00:00
-- url     : https://prove2.me/theorems/0dc8df38-1c0e-4541-988e-73a691034e19
-- title:
--   Triangle bound for autocorrelations: $(v \star v)(y) \le (2M - |y|)_+$
-- statement:
--   For $v : \mathbb{R} \to \mathbb{R}$, the autocorrelation is $(v \star v)(y) = \int_{\mathbb{R}} v(u)\,v(u+y)\,du$ (`Params.autocorr`).
--
--   Suppose $0 \le v \le 1$ pointwise and $v$ vanishes off $(-M, M)$, i.e. $v(u) = 0$ whenever $|u| \ge M$. Then for every real $y$,
--
--   $$(v \star v)(y) \le \max(2M - |y|,\, 0),$$
--
--   the triangle-shaped envelope obtained by comparing $v$ with the indicator of $(-M,M)$.
--
--   Applied to the taper $\varphi$ and to $\varphi^2$, this bounds the autocorrelations $A_\varphi$ and $g$; it is consumed by `Zeta23.PrimeSide.localHyps_concrete`, the concrete verification of the local hypotheses on the prime side of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L58-L81

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

theorem Zeta23.Taper.autocorr_le_of_support (v : ℝ → ℝ) {M : ℝ} (h0 : ∀ u, 0 ≤ v u) (h1 : ∀ u, v u ≤ 1)
    (hz : ∀ u, M ≤ |u| → v u = 0) (y : ℝ) :
    Params.autocorr v y ≤ max (2 * M - |y|) 0 := by sorry
