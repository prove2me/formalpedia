-- Prove2me | Theorems.Thm_Zeta23_EF_abs_mu_le_of_gammaFacts
-- name    : Zeta23.EF.abs_mu_le_of_gammaFacts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:11.355828+00:00
-- url     : https://prove2.me/theorems/5842cc21-5692-4c95-a865-65aa8ea84d80
-- title:
--   Square-root bound $|\mu(\tau)|\le K_2(1+|\tau|)^{1/2}$ for the archimedean density
-- statement:
--   Let $\mu$ be the archimedean density of the explicit formula,
--   $$\mu(\tau)\;=\;\frac{1}{2\pi}\,\mathrm{Re}\,\psi\Bigl(\frac14+\frac{i\tau}{2}\Bigr)\;-\;\frac{\log\pi}{2\pi},$$
--   where $\psi=\Gamma'/\Gamma$ is the digamma function, and let H-$\Gamma$ (`GammaFacts`) be the bundle of Stirling-type facts about $\mu$: evenness, smoothness, monotonicity on $[0,\infty)$, the Stirling asymptotic $\mu(\tau)=\frac{1}{2\pi}\log\frac{|\tau|}{2\pi}+O(\tau^{-2})$ of [eq:mufacts], a derivative bound, and asymptotics for $\int_T^{2T}\mu$ and $\int_T^{2T}\mu^2$.
--
--   Assuming H-$\Gamma$, there exists a constant $K_2\ge 0$ such that for all real $\tau$,
--   $$|\mu(\tau)|\;\le\;K_2\,(1+|\tau|)^{1/2}.$$
--   The proof combines continuity of $\mu$ on $[-1,1]$ with the Stirling asymptotic and the elementary inequality $\log x\le 2\sqrt{x}$ for $|\tau|\ge 1$.
--
--   This crude polynomial bound is consumed by `Zeta23.EF.integrable_paperFT_mul_mu`: paired with the decay $h_k(\tau)\ll(1+\tau^2)^{-1}$ of the Fourier transform of a $C_c^2$ test function, it yields integrability of $h_k\cdot\mu$, one of the analytic inputs to the bridge from the literature-form explicit formula to the paper's form.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula/Bridge.lean#L92-L155, docstring tag [eq:mufacts]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate
set_option backward.isDefEq.respectTransparency false
open Zeta23

theorem Zeta23.EF.abs_mu_le_of_gammaFacts (hΓ : GammaFacts) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ τ : ℝ, |mu τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by sorry
