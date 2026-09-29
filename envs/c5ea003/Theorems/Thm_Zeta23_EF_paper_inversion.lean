-- Prove2me | Theorems.Thm_Zeta23_EF_paper_inversion
-- name    : Zeta23.EF.paper_inversion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:47:29.349062+00:00
-- url     : https://prove2.me/theorems/faf3ef21-eb51-4072-9818-67bbc784fcb2
-- title:
--   Fourier inversion in the paper's normalization: $k(u) = \frac{1}{2\pi}\int h(r)e^{-iru}\,dr$
-- statement:
--   Let $k \colon \mathbb{R} \to \mathbb{C}$ be continuous and integrable, and suppose that its Fourier transform $\mathcal{F}k$ (in Mathlib's normalization $\mathcal{F}k(w) = \int e^{-2\pi i v w} k(v)\,dv$) is also integrable. Write $h(z) = \hat{k}(z) = \int_{\mathbb{R}} k(u)\,e^{izu}\,du$ for the paper's Fourier transform (`paperFT`). Then for every $u \in \mathbb{R}$,
--
--   $$k(u) \;=\; \frac{1}{2\pi} \int_{\mathbb{R}} h(r)\, e^{-iru}\, dr.$$
--
--   This is the inversion formula in the normalization of the paper's Appendix A, obtained from Mathlib's `Continuous.fourierInv_fourier_eq` by the linear substitution $v = -r/(2\pi)$.
--
--   **Role.** In `Zeta23.ExplicitFormula` this converts freely between a Weil test function $k$ and its transform $h$: it feeds the cosine identity $k(y) + k(-y) = \frac{1}{\pi}\int h(\tau)\cos(\tau y)\,d\tau$ (`k_add_k_neg`), the pole-term identification `pole_term`, and the per-$n$ line integral of the Weil explicit formula (`Zeta23.WeilEF.per_n_line_integral`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L131-L155, docstring reference App. A

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

theorem Zeta23.EF.paper_inversion {k : ℝ → ℂ} (hk : Continuous k) (hki : Integrable k)
    (hFk : Integrable (𝓕 k)) (u : ℝ) :
    k u = (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * cexp (-I * r * u) := by sorry
