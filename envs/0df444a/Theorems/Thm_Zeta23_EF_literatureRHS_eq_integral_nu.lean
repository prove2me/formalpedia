-- Prove2me | Theorems.Thm_Zeta23_EF_literatureRHS_eq_integral_nu
-- name    : Zeta23.EF.literatureRHS_eq_integral_nu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:15.462679+00:00
-- url     : https://prove2.me/theorems/3b79e6d6-48fe-4559-9078-f79ae36c5786
-- title:
--   The three identifications: literature RHS of the explicit formula equals $\int h_k\,\nu_X$
-- statement:
--   For a test function $k$ write $h_k(z)=\int_{\mathbb{R}}k(u)e^{izu}\,du$ (`paperFT`). The literature right-hand side (`literatureRHS`, [eq:EFstd]) is
--   $$h_k(\tfrac{i}{2})+h_k(-\tfrac{i}{2})-\sum_{n\ge 1}\frac{\Lambda(n)}{\sqrt n}\bigl(k(\log n)+k(-\log n)\bigr)+\frac{1}{2\pi}\int_{\mathbb{R}}h_k(r)\Bigl[\mathrm{Re}\,\psi\bigl(\tfrac14+\tfrac{ir}{2}\bigr)-\log\pi\Bigr]dr,$$
--   and $\nu_X=\mu+\Pi_X+P_X$ is the paper's zero-counting density (archimedean term $\mu$, pole term $\Pi_X$, prime term $P_X(\tau)=-\frac{1}{\pi}\sum_{n\le X}\frac{\Lambda(n)}{\sqrt n}\cos(\tau\log n)$).
--
--   Suppose $L>0$, $k$ is continuous with (closed) support contained in $[-L,L]$, Mathlib's Fourier transform $\mathcal{F}k$ is integrable, and $\tau\mapsto h_k(\tau)\mu(\tau)$ is integrable. Then
--   $$\mathrm{literatureRHS}(k)\;=\;\int_{\mathbb{R}}h_k(\tau)\,\nu_{X}(\tau)\,d\tau,\qquad X=e^{L}.$$
--
--   This is the step of Appendix A summarized as "adding the three identifications gives (eq:EF)": the Gamma-factor integral matches $\int h_k\mu$, the pole terms match $\int h_k\Pi_X$, and the prime sum matches $\int h_k P_X$ (the support condition $\mathrm{supp}\,k\subseteq[-L,L]$ ensures the prime sum only sees $n\le X$). It is consumed by `Zeta23.EF.prop_EF_of_lit`, which turns the literature-form explicit formula into the paper's form.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L679-L695, docstring tag [eq:EF]

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

theorem Zeta23.EF.literatureRHS_eq_integral_nu {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (𝓕 k))
    (hμ : Integrable (fun τ : ℝ => paperFT k τ * (mu τ : ℂ))) :
    literatureRHS k = ∫ τ : ℝ, paperFT k τ * (nuX (Real.exp L) τ : ℂ) := by sorry
