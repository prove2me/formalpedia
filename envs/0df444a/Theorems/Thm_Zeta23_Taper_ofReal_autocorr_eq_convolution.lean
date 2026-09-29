-- Prove2me | Theorems.Thm_Zeta23_Taper_ofReal_autocorr_eq_convolution
-- name    : Zeta23.Taper.ofReal_autocorr_eq_convolution
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:33:51.158569+00:00
-- url     : https://prove2.me/theorems/ec399584-aac7-4f86-917e-eddb4c7bd893
-- title:
--   For even $v$, the autocorrelation $v \star v$ is the convolution $v_{\mathbb{C}} \ast v_{\mathbb{C}}$
-- statement:
--   For a real function $v$ on $\mathbb{R}$, the project defines the autocorrelation $(v \star v)(y) := \int_{\mathbb{R}} v(u)\,v(u+y)\,du$ (`Params.autocorr`), whereas Mathlib's `convolution` of the complexifications is $(v_{\mathbb{C}} \ast v_{\mathbb{C}})(y) = \int_{\mathbb{R}} v(t)\,v(y-t)\,dt$ (with respect to complex multiplication and Lebesgue measure).
--
--   The theorem asserts that if $v$ is even, $v(-u) = v(u)$ for all $u$, then these two objects agree as functions $\mathbb{R} \to \mathbb{C}$:
--   $$\big(y \mapsto (v \star v)(y)\big) \;=\; v_{\mathbb{C}} \ast v_{\mathbb{C}},$$
--   by the substitution $u = -t$ combined with evenness. No integrability is assumed: when the defining integrals diverge, both sides are interpreted with Lean's convention that a non-integrable Bochner integral is $0$, and the identity is an equality of the defining integrals for each $y$.
--
--   This dictionary lemma lets the project apply Mathlib's convolution theorem to the paper's autocorrelations: it feeds `Zeta23.Taper.paperFT_autocorr` (the identity $(v \star v)^{\wedge} = (\hat v)^2$) and thence the Fourier evaluations `integral_PhiR_sq_mul_cos` and `integral_phiHatR_sq_mul_cos`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Fourier.lean#L171-L182

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

theorem Zeta23.Taper.ofReal_autocorr_eq_convolution (hv : ∀ u, v (-u) = v u) :
    (fun y => (Params.autocorr v y : ℂ)) =
      convolution (fun u => (v u : ℂ)) (fun u => (v u : ℂ)) (ContinuousLinearMap.mul ℂ ℂ)
        volume := by sorry
