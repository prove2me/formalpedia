-- Prove2me | Theorems.Thm_Zeta23_EF_integral_exp_neg_abs_half
-- name    : Zeta23.EF.integral_exp_neg_abs_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:47:17.249521+00:00
-- url     : https://prove2.me/theorems/5b6c1baf-bcce-41c4-ada0-e9a860d5ed53
-- title:
--   Lorentzian Fourier integral $\int_{\mathbb{R}}e^{-|u|/2}e^{-i\tau u}\,du=\bigl(\tfrac14+\tau^{2}\bigr)^{-1}$
-- statement:
--   For every real $\tau$,
--   $$\int_{\mathbb{R}}e^{-|u|/2}\,e^{-i\tau u}\,du\;=\;\frac{1}{\tfrac14+\tau^{2}}.$$
--   This is the classical computation of the Fourier transform of the two-sided exponential $e^{-|u|/2}$, evaluating to the Lorentzian $(\tfrac14+\tau^2)^{-1}$ (the equality is between complex numbers; the imaginary parts of the two half-line contributions cancel).
--
--   In the Appendix A computation of the explicit formula, this identity produces the $X$-independent part $\frac{1}{2\pi(1/4+\tau^2)}$ of the pole density $\Pi_X$, i.e. the contribution of $h_k(\pm i/2)$ from the pole of $\zeta$ rewritten as a density on the critical line. It is consumed by `Zeta23.EF.integrable_paperFT_mul_PiX` and `Zeta23.EF.pole_term`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L456-L488

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

theorem Zeta23.EF.integral_exp_neg_abs_half (τ : ℝ) :
    ∫ u : ℝ, (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u) = 1 / ((1 / 4 : ℂ) + τ ^ 2) := by sorry
