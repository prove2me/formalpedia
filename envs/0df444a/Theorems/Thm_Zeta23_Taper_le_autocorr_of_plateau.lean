-- Prove2me | Theorems.Thm_Zeta23_Taper_le_autocorr_of_plateau
-- name    : Zeta23.Taper.le_autocorr_of_plateau
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:35:52.147055+00:00
-- url     : https://prove2.me/theorems/5698a97b-8d22-4729-946c-0ac5af69795c
-- title:
--   Plateau lower bound for autocorrelations: $(2M - |y|)_+ \le (v \star v)(y)$
-- statement:
--   For a real function $v$ on $\mathbb{R}$, write $(v \star v)(y) := \int_{\mathbb{R}} v(u)\,v(u+y)\,du$ for its autocorrelation (the project's `Params.autocorr`).
--
--   Suppose $v \ge 0$ everywhere, $v = 1$ on the plateau $[-M, M]$, and (for the given shift $y$) the integrand $u \mapsto v(u)v(u+y)$ is integrable. Then the autocorrelation dominates the triangular function:
--   $$\max\big(2M - |y|,\ 0\big) \;\le\; (v \star v)(y).$$
--   Indeed, on the interval where both $u$ and $u+y$ lie in $[-M,M]$ — an interval of length $(2M-|y|)_+$ — the integrand equals $1$, and it is nonnegative elsewhere.
--
--   In the project this comparison is used in `Zeta23.PrimeSide.localHyps_concrete` to bound autocorrelations of the taper $\varphi$ (and of $\varphi^2$) from below by explicit triangular profiles when verifying the local prime-side hypotheses.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Decay.lean#L83-L103

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

theorem Zeta23.Taper.le_autocorr_of_plateau (v : ℝ → ℝ) {M : ℝ} (h0 : ∀ u, 0 ≤ v u)
    (hp : ∀ u, |u| ≤ M → v u = 1) {y : ℝ} (hint : Integrable fun u => v u * v (u + y)) :
    max (2 * M - |y|) 0 ≤ Params.autocorr v y := by sorry
