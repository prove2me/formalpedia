-- Prove2me | Theorems.Thm_Zeta23_WeilEF_gammaR_bracket
-- name    : Zeta23.WeilEF.gammaR_bracket
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:52:16.342049+00:00
-- url     : https://prove2.me/theorems/a8b9d2b1-d566-4388-9025-7aeb4b9137f2
-- title:
--   Critical-line $\Gamma_{\mathbb{R}}$ bracket: sum of $\Gamma_{\mathbb{R}}'/\Gamma_{\mathbb{R}}$ at $\tfrac12 \pm it$ equals $\operatorname{Re}\psi(\tfrac14+\tfrac{it}2) - \log\pi$
-- statement:
--   Let $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ be the Archimedean Gamma factor and $\psi$ the digamma function.
--
--   For every real $t$,
--   $$\frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}\Bigl(\frac12 + it\Bigr) + \frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}\Bigl(\frac12 - it\Bigr) \;=\; \operatorname{Re}\,\psi\Bigl(\frac14 + \frac{it}{2}\Bigr) \;-\; \log\pi,$$
--   where the right-hand side is a real number regarded as a complex number. The proof combines the formula $\operatorname{logDeriv}\Gamma_{\mathbb{R}}(s) = -\tfrac{\log\pi}{2} + \tfrac12\,\psi(s/2)$ (`logDeriv_GammaR`) with the conjugation symmetry $\psi(\overline{z}) = \overline{\psi(z)}$ (`digamma_conj`): the two terms are complex conjugates of one another, so their sum is twice the real part.
--
--   This identifies the two-sided Archimedean contribution on the critical line with exactly the $\Gamma$-integrand appearing in the literal Weil explicit formula `EF_lit_zeta`, which consumes this lemma.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/GammaRBracket.lean#L93-L126

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

theorem Zeta23.WeilEF.gammaR_bracket (t : ℝ) :
    logDeriv Complex.Gammaℝ (1/2 + t * I) + logDeriv Complex.Gammaℝ (1/2 - t * I)
      = (((Complex.digamma (1/4 + t/2 * I)).re - Real.log Real.pi : ℝ) : ℂ) := by sorry
