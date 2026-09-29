-- Prove2me | Theorems.Thm_Zeta23_EF_prime_term
-- name    : Zeta23.EF.prime_term
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:03.023743+00:00
-- url     : https://prove2.me/theorems/ad22914b-7d32-45e1-a969-65d6bd81371b
-- title:
--   Prime term of the explicit formula: $-\sum_n \frac{\Lambda(n)}{\sqrt n}(k(\log n)+k(-\log n)) = \int h\,P_X$
-- statement:
--   Let $L > 0$ and let $k \colon \mathbb{R} \to \mathbb{C}$ be continuous with closed support contained in $[-L, L]$ and with integrable Fourier transform $\mathcal{F}k$; write $h(\tau) = \int k(u)e^{i\tau u}\,du$ and $X = e^{L}$. Then
--
--   $$-\sum_{n \in \mathbb{N}} \frac{\Lambda(n)}{\sqrt{n}}\,\bigl(k(\log n) + k(-\log n)\bigr) \;=\; \int_{\mathbb{R}} h(\tau)\, P_X(\tau)\, d\tau,$$
--
--   where the left side is a `tsum` over all natural numbers (only $0 < n \le \lfloor X \rfloor$ contribute, by the support step `prime_summand_eq_zero`), $\Lambda$ is the von Mangoldt function, and $P_X(\tau) = -\frac{1}{\pi}\sum_{0 < n \le \lfloor X \rfloor} \frac{\Lambda(n)}{\sqrt n}\cos(\tau \log n)$ is the prime density [eq:Pdef]. The proof uses the inversion-derived cosine formula $k(y) + k(-y) = \frac{1}{\pi}\int h(\tau)\cos(\tau y)\,d\tau$.
--
--   **Role.** This is the prime-side identification of the paper's Appendix A, rewriting the von Mangoldt sum of the literature explicit formula [eq:EFstd] as an integral against $P_X$. It is consumed by `Zeta23.EF.literatureRHS_eq_integral_nu`, which assembles $\nu_X = \mu + \Pi_X + P_X$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L335-L367

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

theorem Zeta23.EF.prime_term {k : ℝ → ℂ} {L : ℝ} (hk : Continuous k)
    (hks : tsupport k ⊆ Icc (-L) L) (hFk : Integrable (𝓕 k)) :
    -(∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)))
      = ∫ τ : ℝ, paperFT k τ * (PX (Real.exp L) τ : ℂ) := by sorry
