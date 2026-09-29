-- Prove2me | Theorems.Thm_Zeta23_WeilEF_logDeriv_GammaR
-- name    : Zeta23.WeilEF.logDeriv_GammaR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:50:19.939167+00:00
-- url     : https://prove2.me/theorems/8ab616e8-9e18-41da-aa7c-9a703770d8e8
-- title:
--   $\operatorname{logDeriv}\Gamma_{\mathbb{R}}(s) = -\tfrac{\log\pi}{2} + \tfrac12\,\psi(s/2)$ on the right half-plane
-- statement:
--   Let $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\,\Gamma(s/2)$ be the Archimedean Gamma factor, $\operatorname{logDeriv} f = f'/f$, and $\psi$ the digamma function (Mathlib's `Complex.digamma`).
--
--   For every $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$,
--   $$\frac{\Gamma_{\mathbb{R}}'}{\Gamma_{\mathbb{R}}}(s) \;=\; -\frac{\log\pi}{2} \;+\; \frac{1}{2}\,\psi\!\left(\frac{s}{2}\right).$$
--   This follows from logarithmic differentiation of the product $\pi^{-s/2}\,\Gamma(s/2)$: the exponential factor contributes $-\tfrac{\log \pi}{2}$ and the Gamma factor contributes $\tfrac12\psi(s/2)$ by the chain rule.
--
--   This closed form is the workhorse for all Archimedean estimates in the Weil explicit-formula development: it feeds the continuity lemma `continuous_logDeriv_GammaR_line`, the critical-line bracket `gammaR_bracket`, the vanishing of horizontal pieces `horizontal_vanish`, the integrability lemma `integrable_mul_logDeriv_GammaR_of_decay`, and the norm bound `norm_logDeriv_GammaR_le`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/GammaRBracket.lean#L52-L91

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

theorem Zeta23.WeilEF.logDeriv_GammaR {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -((Real.log Real.pi : ℝ) : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2) := by sorry
