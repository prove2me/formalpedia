-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_digamma_eq
-- name    : Zeta23.StirlingVert.digamma_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:43:35.715258+00:00
-- url     : https://prove2.me/theorems/1cccacf5-e2e5-4a5e-b25a-94dc413c9a35
-- title:
--   Exact digamma formula: $\psi(w) = \log(1+w) - \tfrac1w - \tfrac{1}{2(1+w)} - \tfrac12\sum\rho_n + \sum\varepsilon_m$
-- statement:
--   Fix $w \in \mathbb{C}$ with $\operatorname{Re} w > 0$ and $|\operatorname{Im} w| \ge 1/2$. Define the two families of remainders used throughout the vertical Stirling development:
--   * the second-order telescoping remainder $\rho_n(w) := \dfrac{1}{(n+1+w)^2\,(n+2+w)}$ for $n \in \mathbb{N}$;
--   * the per-interval integral remainder $\varepsilon_m(w) := \displaystyle\int_m^{m+1} \frac{(x-m)^2}{(m+w)^2\,(x+w)}\,dx$ for real $m \ge 0$.
--
--   **Statement** (an exact identity, no error terms):
--   $$\psi(w) \;=\; \log(1+w) \;-\; \frac{1}{w} \;-\; \frac{1}{2(1+w)} \;-\; \frac{1}{2}\sum_{n=0}^{\infty} \rho_n(w) \;+\; \sum_{n=0}^{\infty} \varepsilon_{n+1}(w),$$
--   where $\psi$ is `Complex.digamma`, $\log$ is the principal branch `Complex.log`, and both series are `tsum`s (shown convergent en route).
--
--   This closed form is produced by comparing the digamma partial-fraction series with telescoping logarithms and the harmonic-sum limit, entirely without Euler-Maclaurin. Its sole consumer is `Zeta23.StirlingVert.digamma_stirling`, which bounds the two remainder series to obtain Stirling's asymptotic $\psi(w) = \log w - \frac{1}{2w} + O(1/(\operatorname{Im} w)^2)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L430-L460

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

theorem Zeta23.StirlingVert.digamma_eq (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by sorry
