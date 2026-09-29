-- Prove2me | Theorems.Thm_Zeta23_Taper_autocorr_continuous_of_support
-- name    : Zeta23.Taper.autocorr_continuous_of_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:47:34.417838+00:00
-- url     : https://prove2.me/theorems/daf920b2-e722-4dbf-b63c-476a1522d11d
-- title:
--   Continuity of the autocorrelation $v \star v$ for compactly supported $v$
-- statement:
--   For $v : \mathbb{R} \to \mathbb{R}$, the autocorrelation is $(v \star v)(y) = \int_{\mathbb{R}} v(u)\,v(u+y)\,du$ (`Params.autocorr`).
--
--   Suppose $v$ is continuous and vanishes off $(-M, M)$, i.e. $v(u) = 0$ whenever $|u| \ge M$. Then the function $y \mapsto (v \star v)(y)$ is continuous on $\mathbb{R}$.
--
--   This is a supporting lemma in the `Zeta23.Taper.Decay` module for the autocorrelations $A_\varphi = \varphi \star \varphi$ and $g = \varphi^2 \star \varphi^2$ built from the taper, which enter the Fourier-inversion identities for $\hat\varphi^2$ and $\Phi^2$ used on the prime side of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L120-L135

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

theorem Zeta23.Taper.autocorr_continuous_of_support (v : ℝ → ℝ) {M : ℝ} (hc : Continuous v)
    (hz : ∀ u, M ≤ |u| → v u = 0) : Continuous (Params.autocorr v) := by sorry
