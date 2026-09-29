-- Prove2me | Theorems.Thm_Zeta23_EF_norm_fourier_mul_one_add_sq_le
-- name    : Zeta23.EF.norm_fourier_mul_one_add_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:27.497858+00:00
-- url     : https://prove2.me/theorems/5eb990fc-cb74-439b-a2b2-2c348d802607
-- title:
--   Decay of the Fourier transform of a $C_c^2$ function: $\|\mathcal{F}k(w)\|(1+w^2)\le\|k\|_1+\|k''\|_1/(4\pi^2)$
-- statement:
--   Let $k:\mathbb{R}\to\mathbb{C}$ be twice continuously differentiable and compactly supported — the support hypothesis is phrased as: there is a real $R$ (called $\Lambda$ in the Lean statement, unrelated to the von Mangoldt function) with $k(u)\ne 0\Rightarrow|u|\le R$. Let $\mathcal{F}k$ denote Mathlib's Fourier transform, $\mathcal{F}k(w)=\int_{\mathbb{R}}k(u)e^{-2\pi iuw}\,du$. Then for every real $w$,
--   $$\|\mathcal{F}k(w)\|\,(1+w^{2})\;\le\;\int_{\mathbb{R}}\|k(u)\|\,du\;+\;\frac{1}{4\pi^{2}}\int_{\mathbb{R}}\|k''(u)\|\,du.$$
--
--   This is [eq:hfbound] on the real line: the trivial bound $\|\mathcal{F}k\|\le\|k\|_1$ combined with two integrations by parts, $\mathcal{F}(k'')(w)=-4\pi^2w^2\,\mathcal{F}k(w)$, giving the quantitative decay $\mathcal{F}k(w)\ll(1+w^2)^{-1}$.
--
--   This decay estimate is used throughout the explicit-formula analysis to integrate $h_k$ against densities of logarithmic growth: it is consumed by `Zeta23.EF.explicitFormulaPaper_of_lit` and `Zeta23.EF.integrable_paperFT_mul_mu` (the bridge to the paper's explicit formula) and by `Zeta23.WeilEF.line_integral_swap` and `Zeta23.WeilEF.per_n_line_integral` (the contour-integral derivation of the Weil explicit formula).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula/Bridge.lean#L40-L63, docstring tag [eq:hfbound]

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

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate
set_option backward.isDefEq.respectTransparency false

theorem Zeta23.EF.norm_fourier_mul_one_add_sq_le {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) {Λ : ℝ}
    (hΛ : ∀ u, k u ≠ 0 → |u| ≤ Λ) (w : ℝ) :
    ‖𝓕 k w‖ * (1 + w ^ 2)
      ≤ (∫ u, ‖k u‖) + (∫ u, ‖deriv (deriv k) u‖) / (4 * π ^ 2) := by sorry
