-- Prove2me | Theorems.Thm_Zeta23_EF_integrable_paperFT_mul_PiX
-- name    : Zeta23.EF.integrable_paperFT_mul_PiX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:47:22.906709+00:00
-- url     : https://prove2.me/theorems/065837c5-0247-4784-88fa-c90cb677cce7
-- title:
--   Integrability of $h_k\cdot\Pi_X$ on the real line
-- statement:
--   For a test function $k$ write $h_k(z)=\int_{\mathbb{R}}k(u)e^{izu}\,du$ (`paperFT`), and let $\Pi_X$ be the pole density of the explicit formula ([eq:Pidef]):
--   $$\Pi_X(\tau)\;=\;\frac{1}{2\pi\,(\tfrac14+\tau^2)}\;+\;\frac{1}{\pi}\,\mathrm{Re}\,\frac{X^{s}-1}{s},\qquad s=\frac12+i\tau.$$
--   Suppose $L>0$ and that Mathlib's Fourier transform $\mathcal{F}k$ is integrable. Then the function
--   $$\tau\;\longmapsto\;h_k(\tau)\,\Pi_{X}(\tau),\qquad X=e^{L},$$
--   is integrable on $\mathbb{R}$.
--
--   $\Pi_X$ collects the contributions $h_k(\pm i/2)$ of the pole of $\zeta$ rewritten as a density on the critical line; its integrability against $h_k$ is one of the three identifications assembling the right-hand side of the explicit formula. The lemma is consumed by `Zeta23.EF.literatureRHS_eq_integral_nu` and `Zeta23.EF.prop_EF_of_lit` in the explicit-formula module.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L629-L648

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

theorem Zeta23.EF.integrable_paperFT_mul_PiX {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ * (PiX (Real.exp L) τ : ℂ)) := by sorry
