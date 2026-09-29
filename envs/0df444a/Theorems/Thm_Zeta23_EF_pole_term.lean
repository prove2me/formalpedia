-- Prove2me | Theorems.Thm_Zeta23_EF_pole_term
-- name    : Zeta23.EF.pole_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:47:34.910633+00:00
-- url     : https://prove2.me/theorems/7ce3d017-e7f1-4414-9b2b-74fb6052566b
-- title:
--   Pole term of the explicit formula: $h(i/2)+h(-i/2)=\int h\,\Pi_X$
-- statement:
--   Let $L > 0$ and let $k \colon \mathbb{R} \to \mathbb{C}$ be continuous with closed support contained in $[-L, L]$ and with integrable Fourier transform $\mathcal{F}k$. Write $h(z) = \int_{\mathbb{R}} k(u)e^{izu}\,du$ for the paper Fourier transform of $k$ (`paperFT`, defined for all complex $z$), and set $X = e^{L}$. Then
--
--   $$h(i/2) + h(-i/2) \;=\; \int_{\mathbb{R}} h(\tau)\,\Pi_X(\tau)\,d\tau,$$
--
--   where $\Pi_X$ is the pole density of [eq:Pidef], $\Pi_X(\tau) = \dfrac{1}{2\pi(1/4+\tau^2)} + \dfrac{1}{\pi}\,\operatorname{Re}\dfrac{X^{s}-1}{s}$ with $s = \tfrac12 + i\tau$. The proof rests on the two elementary integrals $\int_{\mathbb{R}} e^{-|u|/2} e^{-i\tau u}\,du = (1/4+\tau^2)^{-1}$ and $\int_{-L}^{L} e^{|u|/2} e^{-i\tau u}\,du = 2\operatorname{Re}((X^{s}-1)/s)$.
--
--   **Role.** This is one of the three identifications of the paper's Appendix A: it rewrites the contribution $h(\pm i/2)$ of the pole of $\zeta$ at $s=1$ as an integral against the density $\Pi_X$. It is consumed by `Zeta23.EF.literatureRHS_eq_integral_nu`, which assembles the literature explicit formula [eq:EFstd] into the paper's density form with $\nu_X = \mu + \Pi_X + P_X$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L554-L625

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

theorem Zeta23.EF.pole_term {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (𝓕 k)) :
    paperFT k (I / 2) + paperFT k (-I / 2)
      = ∫ τ : ℝ, paperFT k τ * (PiX (Real.exp L) τ : ℂ) := by sorry
