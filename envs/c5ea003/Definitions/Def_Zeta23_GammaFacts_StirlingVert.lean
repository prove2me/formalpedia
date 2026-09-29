-- Prove2me | Definitions.Def_Zeta23_GammaFacts_StirlingVert
-- name    : Zeta23_GammaFacts_StirlingVert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:06:34.02189+00:00
-- url     : https://prove2.me/theorems/0e802e66-c4b0-4e15-884f-2d7955186181
-- title:
--   Remainder terms for Stirling on vertical lines
-- statement:
--   This bundle defines the two remainder terms of `Zeta23/GammaFacts/StirlingVert.lean`, which proves Stirling's formula for the digamma function on vertical lines — the complex asymptotic $\psi(w) = \log w - \frac{1}{2w} + O(1/(\mathrm{Im}\,w)^2)$ for $0 < \mathrm{Re}\,w \le 1$, $|\mathrm{Im}\,w| \ge 1$ — from the partial-fraction series, without Euler–Maclaurin.
--
--   **`eps`** is the per-interval remainder: for $w \in \mathbb{C}$ and $m \in \mathbb{R}$,
--   $$\varepsilon_m(w) := \int_m^{m+1} \frac{(x - m)^2}{(m + w)^2 (x + w)}\,dx,$$
--   arising from the exact algebraic identity $\frac{1}{x+w} = \frac{1}{m+w} - \frac{x-m}{(m+w)^2} + \frac{(x-m)^2}{(m+w)^2(x+w)}$, so that $\int_m^{m+1}\frac{dx}{x+w} = \frac{1}{m+w} - \frac{1}{2(m+w)^2} + \varepsilon_m$ with $|\varepsilon_m| \le 1/(3|m+w|^2|\mathrm{Im}\,w|)$, while the left side telescopes as $\log(m+1+w) - \log(m+w)$.
--
--   **`rho`** is the second-order telescoping remainder: with $z_n := n + 1 + w$,
--   $$\rho_n := \frac{1}{z_n^2\, z_{n+1}}.$$
--
--   Summing these remainders yields the H-Γ field `GammaFacts.stirling`, $\mu(\tau) = \frac{1}{2\pi}\log\frac{|\tau|}{2\pi} + O(\tau^{-2})$ for $|\tau| \ge 1$ [eq:mufacts], discharging the Stirling hypothesis used by `IntMu.lean` and completing the Γ-facts package consumed by the prime-side traces of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean, docstring tag [eq:mufacts]

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

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/StirlingVert.lean — Stirling for the digamma function on vertical lines.  Target: the H-Γ field `GammaFacts.stirling`
  "μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²)  (|τ| ≥ 1)"   [eq:mufacts]
via the COMPLEX asymptotic  ψ(w) = log w − 1/(2w) + O(1/(Im w)²)  for 0 < Re w ≤ 1,
|Im w| ≥ 1, proved from the partial-fraction series (Zeta23.DigammaSeries)
WITHOUT Euler–Maclaurin:  on each unit interval
   1/(x+w) = 1/(m+w) − (x−m)/(m+w)² + (x−m)²/((m+w)²(x+w))        (exact algebra),
so ∫_m^{m+1} dx/(x+w) = 1/(m+w) − 1/(2(m+w)²) + ε_m, |ε_m| ≤ 1/(3|m+w|²|Im w|), while the
left side is log(m+1+w) − log(m+w) (FTC for Complex.log on the slit plane) and telescopes.
-/

noncomputable section

namespace Zeta23
namespace StirlingVert

open Complex Filter Topology MeasureTheory intervalIntegral Set

/-! ### ℂ-specialized interval-integral constant rules (the RCLike-generic Mathlib versions do
not match ℂ's default instance path under `rw`; cf. Zeta23.integral_const_mul_C) -/



/-! ### Elementary bounds for points in the right half-plane -/





/-! ### The antiderivative `F(x) = log(x + w)` on `[0, ∞)` -/



/-! ### The per-interval expansion -/


/-- the per-interval remainder `ε_m(w) := ∫_m^{m+1} (x−m)²/((m+w)²(x+w)) dx`. -/
def eps (w : ℂ) (m : ℝ) : ℂ :=
  ∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))



/-! ### The sequence `z_n := n + 1 + w` -/

section Seq
variable {w : ℂ}







/-- the second-order telescoping remainder `ρ_n := 1/(z_n² z_{n+1})`. -/
def rho (w : ℂ) (n : ℕ) : ℂ := 1 / (((n : ℂ) + 1 + w) ^ 2 * ((n : ℂ) + 2 + w))





/-! ### Bounds: `Σ_{n<N} 1/‖z_n‖² ≤ 2/|im w|` by a real telescoping -/




/-! ### Summability of the remainders and tsum bounds -/









/-! ### Limits -/



/-! ### The exact identity and the Stirling bound -/





end Seq

/-! ### Real part on vertical lines, and the H-Γ field for μ -/

section RePart




end RePart

end StirlingVert
end Zeta23


