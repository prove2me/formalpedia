-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_tendsto_harmonic_sub_clog
-- name    : Zeta23.StirlingVert.tendsto_harmonic_sub_clog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:43:29.279989+00:00
-- url     : https://prove2.me/theorems/64708afb-a372-4493-9a65-82f3926cf806
-- title:
--   Shifted harmonic-logarithm limit: $\sum_{n<N}\frac{1}{n+1} - \log(N+1+w) \to \gamma$
-- statement:
--   Fix $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$. Then, as $N \to \infty$ through the natural numbers,
--   $$\sum_{n < N} \frac{1}{n+1} \;-\; \log\bigl(N + 1 + w\bigr) \;\longrightarrow\; \gamma,$$
--   where the sum is the $N$-th harmonic number (viewed in $\mathbb{C}$), $\log$ is the principal complex logarithm `Complex.log`, and $\gamma$ is the Euler-Mascheroni constant (`Real.eulerMascheroniConstant`, coerced to $\mathbb{C}$). The convergence is stated as a filter limit (`Tendsto ... atTop`).
--
--   The point is that the shift by the fixed complex number $w$ inside the logarithm does not change the classical limit $H_N - \log N \to \gamma$, since $\log(N+1+w) - \log N \to 0$ for $\operatorname{Re} w > 0$.
--
--   Its sole consumer is `Zeta23.StirlingVert.digamma_eq`: passing to the limit in the rearranged partial sums `partial_sum_eq`, this limit supplies the constant $-\gamma$ hidden in the digamma series and produces the exact closed formula for $\psi(w)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L373-L415

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

theorem Zeta23.StirlingVert.tendsto_harmonic_sub_clog (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1))
      - Complex.log ((N : ℂ) + 1 + w)) atTop (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by sorry
