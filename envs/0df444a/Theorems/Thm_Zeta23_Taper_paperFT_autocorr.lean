-- Prove2me | Theorems.Thm_Zeta23_Taper_paperFT_autocorr
-- name    : Zeta23.Taper.paperFT_autocorr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:34:01.979883+00:00
-- url     : https://prove2.me/theorems/6ce65d71-dcfd-4ff8-9d8f-03fc70a54fef
-- title:
--   Convolution theorem for autocorrelations: $(v \star v)^{\wedge}(r) = \hat v(r)^2$
-- statement:
--   For a real function $v$ on $\mathbb{R}$, let $(v \star v)(y) := \int_{\mathbb{R}} v(u)\,v(u+y)\,du$ be its autocorrelation, and let $h_f(z) := \int f(u)e^{izu}\,du$ denote the paper Fourier transform `paperFT`.
--
--   The theorem asserts: if $v$ is even ($v(-u) = v(u)$), continuous, and compactly supported, then for every real $r$
--   $$\big(v \star v\big)^{\wedge}(r) \;=\; \big(\hat v(r)\big)^2,$$
--   i.e. the paper transform of the (complexified) autocorrelation at $r$ equals the square of the paper transform of $v$ at $r$. This is the paper's convolution identity "$(f * g)^{\wedge} = \hat f\, \hat g$" from [Notation], transported through the dictionary between `paperFT` and Mathlib's Fourier transform via `Real.fourier_mul_convolution_eq` and the preceding lemma `ofReal_autocorr_eq_convolution`.
--
--   In the project it is the key step in evaluating the second moments of the taper transforms: it feeds `Zeta23.Taper.integral_PhiR_sq_mul_cos` and `Zeta23.Taper.integral_phiHatR_sq_mul_cos`, the Plancherel-type identities of [eq:Phi2FT] used on the prime side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L204-L213, docstring tag [Notation]

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
open scoped FourierTransform ComplexConjugate
open Zeta23
variable {v : ℝ → ℝ}

theorem Zeta23.Taper.paperFT_autocorr (hv : ∀ u, v (-u) = v u) (hc : Continuous v) (hs : HasCompactSupport v)
    (r : ℝ) :
    paperFT (fun y => (Params.autocorr v y : ℂ)) r = (paperFT (fun u => (v u : ℂ)) r) ^ 2 := by sorry
