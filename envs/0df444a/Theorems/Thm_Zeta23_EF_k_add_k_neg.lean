-- Prove2me | Theorems.Thm_Zeta23_EF_k_add_k_neg
-- name    : Zeta23.EF.k_add_k_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:47:40.573253+00:00
-- url     : https://prove2.me/theorems/f150c72e-aee9-4700-a8ef-a4952af3d66f
-- title:
--   Fourier inversion for the symmetrized test function: $k(y)+k(-y)=\frac{1}{\pi}\int h_k(\tau)\cos(\tau y)\,d\tau$
-- statement:
--   For a test function $k:\mathbb{R}\to\mathbb{C}$ write $h_k(z)=\int_{\mathbb{R}}k(u)e^{izu}\,du$ (`paperFT`). Suppose $k$ is continuous and integrable and that Mathlib's Fourier transform $\mathcal{F}k$ is integrable (so Fourier inversion applies). Then for every real $y$,
--   $$k(y)+k(-y)\;=\;\frac{1}{\pi}\int_{\mathbb{R}}h_k(\tau)\,\cos(\tau y)\,d\tau.$$
--
--   The proof is Fourier inversion applied at $\pm y$ and summed: $k(y)+k(-y)=\frac{1}{2\pi}\int h_k(\tau)(e^{-i\tau y}+e^{i\tau y})\,d\tau=\frac{1}{\pi}\int h_k(\tau)\cos(\tau y)\,d\tau$.
--
--   This is the first step of the prime-term identification in Appendix A: applied at $y=\log n$ and summed against $\Lambda(n)/\sqrt n$, it converts the prime sum of the literature explicit formula into the integral $\int h_k\,P_X$ against the prime density. It is consumed by `Zeta23.EF.prime_term`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L295-L311

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction
set_option backward.isDefEq.respectTransparency false
open Zeta23
open EF

theorem Zeta23.EF.k_add_k_neg {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (y : ℝ) :
    k y + k (-y) = (1 / π : ℂ) * ∫ τ : ℝ, paperFT k τ * (Real.cos (τ * y) : ℂ) := by sorry
