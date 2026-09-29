-- Prove2me | Theorems.Thm_Zeta23_WeilEF_per_n_line_integral
-- name    : Zeta23.WeilEF.per_n_line_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:21.48175+00:00
-- url     : https://prove2.me/theorems/f0ceef13-8e03-460b-8a07-efaf5141d32e
-- title:
--   Per-$n$ line integral: $\frac{1}{2\pi}\int h_{k_b}(t)\,\frac{\Lambda(n)}{n^{c+it}}\,dt = \frac{\Lambda(n)}{\sqrt{n}}\,k(\log n)$
-- statement:
--   Let $k : \mathbb{R} \to \mathbb{C}$ be twice continuously differentiable with compact support, let $c$ be any real number, and let $n \in \mathbb{N}$. Write $h_f(z) = \int f(u) e^{izu} du$ (`paperFT`), and let $k_b(u) := k(u)\, e^{bu}$ denote the tilted test function (`tilt k b`) with tilt $b = c - 1/2$. The factor `LSeries.term (Λ ·) (c+it) n` is Mathlib's $n$-th Dirichlet series term $\Lambda(n)\, n^{-(c+it)}$ for $n \ge 1$, and $0$ for $n = 0$, where $\Lambda$ is the von Mangoldt function.
--
--   **Statement.**
--   $$\frac{1}{2\pi} \int_{\mathbb{R}} h_{k_{c-1/2}}(t)\; \frac{\Lambda(n)}{n^{c+it}}\, dt = \frac{\Lambda(n)}{\sqrt{n}}\; k(\log n).$$
--   This is Fourier inversion applied to a single term of the Dirichlet series for $-\zeta'/\zeta$: the vertical-line average of the test weight against $n^{-(c+it)}$ picks out the value $k(\log n)$, with the tilt by $c - 1/2$ producing the normalising factor $n^{-1/2}$. No hypothesis on $c$ is needed at this per-$n$ level; for $n = 0$ both sides vanish ($\Lambda(0) = 0$).
--
--   **Role.** Summed over $n$ in the module `Zeta23.WeilEF.VerticalLine`, it produces the prime side of the explicit formula on the line $\operatorname{Re} s = c$ (`prime_side_line`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/VerticalLine.lean#L97-L158

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_WeilEF_VerticalLine

open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem Zeta23.WeilEF.per_n_line_integral {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        paperFT (tilt k (c - 1/2)) t * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n
      = ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by sorry
