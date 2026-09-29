-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_partial_sum_eq
-- name    : Zeta23.StirlingVert.partial_sum_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:43:22.907275+00:00
-- url     : https://prove2.me/theorems/3a70ac54-ea90-414a-96d3-3e7c495b4001
-- title:
--   Rearranged partial sums of the digamma series
-- statement:
--   Fix $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$ and $N \in \mathbb{N}$. Using the remainders $\rho_n(w) = \frac{1}{(n+1+w)^2(n+2+w)}$ and $\varepsilon_m(w) = \int_m^{m+1}\frac{(x-m)^2}{(m+w)^2(x+w)}\,dx$, the $N$-th partial sum of the digamma partial-fraction series can be rewritten exactly as
--   $$\sum_{n<N} \Bigl(\frac{1}{n+1} - \frac{1}{w+n+1}\Bigr) \;=\; \sum_{n<N}\frac{1}{n+1} \;-\; \bigl(\log(N+1+w) - \log(1+w)\bigr) \;-\; \frac12\Bigl(\frac{1}{1+w} - \frac{1}{N+1+w} + \sum_{n<N}\rho_n(w)\Bigr) \;+\; \sum_{n<N}\varepsilon_{n+1}(w),$$
--   with $\log$ the principal branch (in the Lean text the two constant terms appear as $((0:\mathbb{N})+1+w)$, i.e. $1+w$).
--
--   This identity (step (I3) of the argument) is obtained by telescoping the unit-interval expansion `integral_inv_add_eq` and the second-order identity for $1/z_n^2$ across $n < N$. Letting $N \to \infty$ against the harmonic-logarithm limit yields the exact digamma formula: its sole consumer is `Zeta23.StirlingVert.digamma_eq`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L235-L257

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert

open Zeta23
open StirlingVert
open Complex Filter Topology MeasureTheory intervalIntegral Set
variable {w : ℂ}

theorem Zeta23.StirlingVert.partial_sum_eq (hw : 0 < w.re) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
      = (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
        - (Complex.log ((N : ℂ) + 1 + w) - Complex.log ((0 : ℕ) + 1 + w : ℂ))
        - (1 / 2 : ℂ) * (((0 : ℕ) + 1 + w : ℂ)⁻¹ - ((N : ℂ) + 1 + w)⁻¹
            + ∑ n ∈ Finset.range N, rho w n)
        + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by sorry
