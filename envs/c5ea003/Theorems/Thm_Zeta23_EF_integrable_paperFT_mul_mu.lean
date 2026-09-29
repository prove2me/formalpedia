-- Prove2me | Theorems.Thm_Zeta23_EF_integrable_paperFT_mul_mu
-- name    : Zeta23.EF.integrable_paperFT_mul_mu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:38.045144+00:00
-- url     : https://prove2.me/theorems/d9609814-72ac-4d31-8b1e-86d39257b146
-- title:
--   Integrability of $h_k\cdot\mu$ for $k\in C_c^2(\mathbb{R})$
-- statement:
--   Let $k:\mathbb{R}\to\mathbb{C}$ be twice continuously differentiable with compact support, write $h_k(z)=\int_{\mathbb{R}}k(u)e^{izu}\,du$ (`paperFT`), and let
--   $$\mu(\tau)\;=\;\frac{1}{2\pi}\,\mathrm{Re}\,\psi\Bigl(\frac14+\frac{i\tau}{2}\Bigr)-\frac{\log\pi}{2\pi}$$
--   be the archimedean density. Assuming the Stirling-type facts H-$\Gamma$ (`GammaFacts`) about $\mu$, the function
--   $$\tau\;\longmapsto\;h_k(\tau)\,\mu(\tau)$$
--   is integrable on $\mathbb{R}$.
--
--   The proof dominates the product by $K\,(1+|\tau|)^{-3/2}$: the Fourier bound [eq:hfbound] gives $|h_k(\tau)|\ll(1+\tau^2)^{-1}$ while `abs_mu_le_of_gammaFacts` gives $|\mu(\tau)|\le K_2(1+|\tau|)^{1/2}$. This integrability is required to even state the Gamma-factor term of the explicit formula as a Lebesgue integral; it is consumed by `Zeta23.EF.explicitFormulaPaper_of_lit`, the bridge from the literature-form to the paper-form explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula/Bridge.lean#L157-L186

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

theorem Zeta23.EF.integrable_paperFT_mul_mu {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (hΓ : GammaFacts) : Integrable (fun τ : ℝ => paperFT k τ * (mu τ : ℂ)) := by sorry
