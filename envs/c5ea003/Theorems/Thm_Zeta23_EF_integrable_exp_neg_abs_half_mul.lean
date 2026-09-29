-- Prove2me | Theorems.Thm_Zeta23_EF_integrable_exp_neg_abs_half_mul
-- name    : Zeta23.EF.integrable_exp_neg_abs_half_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:47:04.47865+00:00
-- url     : https://prove2.me/theorems/35b1b5f8-0cf1-46b2-bbf7-e7b5733abf00
-- title:
--   Integrability of $u\mapsto e^{-|u|/2}e^{-i\tau u}$ on $\mathbb{R}$
-- statement:
--   For every real $\tau$, the function
--   $$u\;\longmapsto\;e^{-|u|/2}\,e^{-i\tau u}$$
--   is (Bochner/Lebesgue) integrable on $\mathbb{R}$. The proof splits $\mathbb{R}$ into the two half-lines, where the modulus $e^{-|u|/2}$ is a decaying exponential.
--
--   This elementary integrability fact underlies the pole-term computation of the explicit formula (Appendix A): the two-sided Laplace-type integral $\int_{\mathbb{R}}e^{-|u|/2}e^{-i\tau u}\,du=(\tfrac14+\tau^2)^{-1}$ produces the Lorentzian part of the pole density $\Pi_X$. It is consumed by `Zeta23.EF.integrable_paperFT_mul_PiX` and `Zeta23.EF.pole_term` in the explicit-formula module.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L429-L450

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

theorem Zeta23.EF.integrable_exp_neg_abs_half_mul (τ : ℝ) :
    Integrable (fun u : ℝ => (Real.exp (-|u| / 2) : ℂ) * cexp (-I * τ * u)) := by sorry
