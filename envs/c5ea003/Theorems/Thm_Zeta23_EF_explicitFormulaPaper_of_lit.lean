-- Prove2me | Theorems.Thm_Zeta23_EF_explicitFormulaPaper_of_lit
-- name    : Zeta23.EF.explicitFormulaPaper_of_lit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:34.664684+00:00
-- url     : https://prove2.me/theorems/e821385a-01db-40f6-8f6c-9170d6f53cb4
-- title:
--   The bridge: literature explicit formula $\Rightarrow$ paper explicit formula
-- statement:
--   Let $Z$ be an abstract zero configuration (`ZeroConfig`): a set of points $\rho$ in the closed strip $0\le\mathrm{Re}\,\rho\le 1$ with multiplicities $m_\rho\ge 1$, invariant (with multiplicity) under the reflection $\rho\mapsto 1-\bar\rho$, and locally finite in the ordinate. For a test function $k$ write $h_k(z)=\int_{\mathbb{R}}k(u)e^{izu}\,du$ (`paperFT`).
--
--   Assume:
--   * **H-EF, literature form** (`EF_lit Z`, [eq:EFstd]): for every $k\in C_c^2(\mathbb{R})$ the zero sum $\sum_\rho m_\rho h_k(\gamma_\rho)$ (where $\rho=\tfrac12+i\gamma_\rho$) converges absolutely and equals
--   $$h_k(\tfrac{i}{2})+h_k(-\tfrac{i}{2})-\sum_{n\ge 1}\frac{\Lambda(n)}{\sqrt n}\bigl(k(\log n)+k(-\log n)\bigr)+\frac{1}{2\pi}\int_{\mathbb{R}}h_k(r)\Bigl[\mathrm{Re}\,\psi\bigl(\tfrac14+\tfrac{ir}{2}\bigr)-\log\pi\Bigr]dr;$$
--   * **H-$\Gamma$** (`GammaFacts`): the Stirling-type facts about the archimedean density $\mu(\tau)=\frac{1}{2\pi}\mathrm{Re}\,\psi(\frac14+\frac{i\tau}{2})-\frac{\log\pi}{2\pi}$.
--
--   Then the paper's explicit formula [prop:EF]/[eq:EF] holds for $Z$ exactly as `Zeta23.ExplicitFormulaPaper` states it: for every $L>0$ and all $f,g\in C_c^2(\mathbb{R})$ supported in $[-L/2,L/2]$, the Weil sum $W(f,g)=\sum_\rho m_\rho\,h_f(\gamma_\rho)\overline{h_g(\overline{\gamma_\rho})}$ is summable, the integrand below is integrable, and
--   $$W(f,g)\;=\;\int_{\mathbb{R}}h_f(\tau)\,\overline{h_g(\tau)}\;\nu_X(\tau)\,d\tau,\qquad X=e^{L},$$
--   where $\nu_X=\mu+\Pi_X+P_X$ is the paper's zero-counting density (archimedean term, pole term, prime term).
--
--   This theorem is the entire content of Appendix A of the paper. It is consumed directly by `Zeta23.thmA3` and `Zeta23.thmA3_cumulative`, the final assemblies of Theorem A, where it converts the classical Weil/Guinand-type explicit formula into the specific form used by the matrix-variational argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula/Bridge.lean#L188-L201, docstring tags [eq:EFstd], [prop:EF], [eq:EF]

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
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_Hypotheses

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate
set_option backward.isDefEq.respectTransparency false
open Zeta23
open EF

theorem Zeta23.EF.explicitFormulaPaper_of_lit (Z : ZeroConfig) (hEF : EF_lit Z) (hΓ : GammaFacts) :
    ExplicitFormulaPaper Z := by sorry
