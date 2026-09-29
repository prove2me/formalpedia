-- Prove2me | Theorems.Thm_Zeta23_EF_paperFT_weilTest
-- name    : Zeta23.EF.paperFT_weilTest
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:21.757847+00:00
-- url     : https://prove2.me/theorems/71c7aa60-7434-47d6-bfdf-fc34a6587eaa
-- title:
--   Multiplicativity of the paper transform under Weil convolution: $h_{f\star\tilde g}(z)=h_f(z)\,\overline{h_g(\bar z)}$
-- statement:
--   For test functions write $h_f(z)=\int_{\mathbb{R}}f(u)e^{izu}\,du$ (`paperFT`), extended to complex arguments $z$. Given $g:\mathbb{R}\to\mathbb{C}$, let $\tilde g(u):=\overline{g(-u)}$, and let the Weil test function be the convolution $k=f\star\tilde g$, i.e. $k(x)=\int_{\mathbb{R}}f(t)\,\tilde g(x-t)\,dt$ (`weilTest`).
--
--   If $f$ and $g$ are continuous with compact support, then for every $z\in\mathbb{C}$,
--   $$h_{f\star\tilde g}(z)\;=\;h_f(z)\cdot\overline{h_g(\bar z)}.$$
--   In particular on the real line $h_{f\star\tilde g}(\tau)=h_f(\tau)\overline{h_g(\tau)}$, and the identity remains valid at complex points such as $z=\gamma_\rho$ for off-line zeros.
--
--   This is the standard Weil positivity structure of Appendix A: choosing $k=f\star\tilde g$ turns the zero sum of the literature explicit formula into the Hermitian form $W(f,g)=\sum_\rho m_\rho h_f(\gamma_\rho)\overline{h_g(\overline{\gamma_\rho})}$. It is consumed by `Zeta23.EF.prop_EF_of_lit`, the derivation of the paper-form explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L188-L236

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

theorem Zeta23.EF.paperFT_weilTest {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) (z : ℂ) :
    paperFT (weilTest f g) z = paperFT f z * conj (paperFT g (conj z)) := by sorry
