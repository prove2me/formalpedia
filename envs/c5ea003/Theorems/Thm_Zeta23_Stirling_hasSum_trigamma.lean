-- Prove2me | Theorems.Thm_Zeta23_Stirling_hasSum_trigamma
-- name    : Zeta23.Stirling.hasSum_trigamma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:55:05.05235+00:00
-- url     : https://prove2.me/theorems/4d62b0a6-3e69-4386-a12c-c85ecf7af77a
-- title:
--   Trigamma series: $\psi'(z) = \sum_{n \ge 0} (z+n)^{-2}$
-- statement:
--   Let $\psi$ be the complex digamma function (`Complex.digamma`). For every $z$ in the integer complement (i.e. $z$ is not an integer), the termwise derivative of the digamma partial-fraction series converges to the actual derivative: the family $\bigl(1/(z+n)^2\bigr)_{n \ge 0}$ is summable with
--   $$\psi'(z) \;=\; \sum_{n=0}^{\infty} \frac{1}{(z+n)^{2}},$$
--   stated in Lean as a `HasSum` for the function $n \mapsto 1/(z+n)^2$ with sum `deriv Complex.digamma z`.
--
--   This is the trigamma expansion, obtained by differentiating the digamma series termwise and justifying the exchange of limit and derivative.
--
--   Its consumer is `Zeta23.MuFields.mu_deriv_bound`: the H-$\Gamma$ clause $\mu'(\tau) \ll |\tau|^{-1}$ for the archimedean density $\mu(\tau) = \frac{1}{2\pi}\operatorname{Re}\psi(\tfrac14 + \tfrac{i\tau}{2}) - \frac{\log\pi}{2\pi}$, which is proved by estimating this series.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Analytic/Stirling.lean#L51-L273

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Complex Filter Topology

theorem Zeta23.Stirling.hasSum_trigamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / (z + n) ^ 2) (deriv Complex.digamma z) := by sorry
