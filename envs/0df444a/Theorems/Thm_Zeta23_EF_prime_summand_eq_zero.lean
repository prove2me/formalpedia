-- Prove2me | Theorems.Thm_Zeta23_EF_prime_summand_eq_zero
-- name    : Zeta23.EF.prime_summand_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:08.768985+00:00
-- url     : https://prove2.me/theorems/68af55ab-5093-48f5-b13b-214bfe254b69
-- title:
--   Support step for the prime term: summands with $n > X$ (or $n = 0$) vanish
-- statement:
--   Let $k \colon \mathbb{R} \to \mathbb{C}$ have closed support contained in $[-L, L]$, and let $n$ be a natural number outside the index range $0 < n \le \lfloor e^{L} \rfloor$ (i.e. $n = 0$ or $n > \lfloor X \rfloor$ with $X = e^{L}$). Then the $n$-th summand of the prime sum in the explicit formula vanishes:
--
--   $$\frac{\Lambda(n)}{\sqrt{n}}\,\bigl(k(\log n) + k(-\log n)\bigr) \;=\; 0,$$
--
--   where $\Lambda$ is the von Mangoldt function. For $n = 0$ this holds because $\Lambda(0) = 0$; for $n > \lfloor X \rfloor$ because $\log n > L$ lies outside the support of $k$, so $k(\pm\log n) = 0$.
--
--   **Role.** This support step shows that the $n$-sum in the literature explicit formula [eq:EFstd], a priori an infinite series over all $n \in \mathbb{N}$, is really the finite sum over $0 < n \le \lfloor X \rfloor$. It is consumed by `Zeta23.EF.prime_term`, the prime-side identification of Appendix A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L313-L333, docstring tag [eq:EFstd]

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

theorem Zeta23.EF.prime_summand_eq_zero {k : ℝ → ℂ} {L : ℝ} (hks : tsupport k ⊆ Icc (-L) L)
    {n : ℕ} (hn : n ∉ Finset.Ioc 0 ⌊Real.exp L⌋₊) :
    ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) = 0 := by sorry
