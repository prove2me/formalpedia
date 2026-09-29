-- Prove2me | Theorems.Thm_Zeta23_EF_integral_EL_mul
-- name    : Zeta23.EF.integral_EL_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:47:10.91065+00:00
-- url     : https://prove2.me/theorems/72f13cbe-5b32-4a11-996f-7bfbe7e0d2aa
-- title:
--   Pole-term integral: $\int_{-L}^{L}e^{|u|/2}e^{-i\tau u}\,du=2\,\mathrm{Re}\,\frac{X^{s}-1}{s}$, $s=\tfrac12+i\tau$, $X=e^{L}$
-- statement:
--   Let $E_L$ be the truncated exponential weight $E_L(u)=e^{|u|/2}\mathbf{1}_{[-L,L]}(u)$ (in Lean, the indicator of $[-L,L]$ applied to $u\mapsto e^{|u|/2}$). For every real $\tau$ and every $L>0$,
--   $$\int_{\mathbb{R}}E_L(u)\,e^{-i\tau u}\,du\;=\;2\,\mathrm{Re}\,\frac{X^{s}-1}{s},\qquad s=\frac12+i\tau,\quad X=e^{L},$$
--   the right-hand side being the real number $2\,\mathrm{Re}((X^s-1)/s)$ regarded as a complex number.
--
--   The computation folds the integral onto $[0,L]$ using the evenness structure, $\int_{-L}^{L}e^{|u|/2}e^{-i\tau u}du=2\,\mathrm{Re}\int_0^L e^{u\bar s}\,du$, and evaluates the elementary integral. This identity produces the $X$-dependent part of the pole density $\Pi_X$ in the explicit formula (the terms $h_k(\pm i/2)$ of the pole of $\zeta$ rewritten as a density on the critical line, Appendix A); it is consumed by `Zeta23.EF.integrable_paperFT_mul_PiX` and `Zeta23.EF.pole_term`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L504-L552

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

theorem Zeta23.EF.integral_EL_mul (τ : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ u : ℝ, EL L u * cexp (-I * τ * u)
      = ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ) := by sorry
