-- Prove2me | Theorems.Thm_Zeta23_WeilEF_digamma_conj
-- name    : Zeta23.WeilEF.digamma_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:52:05.920187+00:00
-- url     : https://prove2.me/theorems/b228a9b7-8543-468c-b2a4-b830a529d781
-- title:
--   Conjugation symmetry of the digamma function
-- statement:
--   Let $\psi = \Gamma'/\Gamma$ denote the digamma function on $\mathbb{C}$ (Mathlib's `Complex.digamma`), and let $\overline{z}$ denote complex conjugation (`starRingEnd`).
--
--   For every $z$ in the integer complement $\mathbb{C} \setminus \mathbb{Z}$ (in particular avoiding the poles of $\psi$ at the nonpositive integers),
--   $$\psi(\overline{z}) \;=\; \overline{\psi(z)}.$$
--   This is the Schwarz reflection property of $\psi$, inherited from $\Gamma(\overline{z}) = \overline{\Gamma(z)}$.
--
--   In the project it is used by `gammaR_bracket` to evaluate the critical-line combination $\operatorname{logDeriv}\Gamma_{\mathbb{R}}(1/2 + it) + \operatorname{logDeriv}\Gamma_{\mathbb{R}}(1/2 - it)$ as the real quantity $\operatorname{Re}\psi(1/4 + it/2) - \log\pi$, the Archimedean integrand of the Weil explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/GammaRBracket.lean#L27-L50

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Complex

theorem Zeta23.WeilEF.digamma_conj {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma (starRingEnd ℂ z) = starRingEnd ℂ (Complex.digamma z) := by sorry
