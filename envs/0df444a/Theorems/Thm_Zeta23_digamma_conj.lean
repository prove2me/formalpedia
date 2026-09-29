-- Prove2me | Theorems.Thm_Zeta23_digamma_conj
-- name    : Zeta23.digamma_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:55:25.742342+00:00
-- url     : https://prove2.me/theorems/1c087765-01f4-40af-88e2-d041f6e42fae
-- title:
--   $\Gamma'/\Gamma$ commutes with complex conjugation
-- statement:
--   For every complex number $z$, Mathlib's digamma function `Complex.digamma` (defined as the logarithmic derivative $\Gamma'/\Gamma$ of the complex Gamma function) satisfies the reflection identity
--   $$\psi(\bar z) \;=\; \overline{\psi(z)},$$
--   where the bar denotes complex conjugation (`starRingEnd ℂ`). The proof derives this from the Schwarz-type symmetry $\Gamma(\bar z) = \overline{\Gamma(z)}$ together with the corresponding rule for derivatives of conjugated functions.
--
--   In the project (module `Zeta23.GammaFacts`) this feeds the evenness clause of [eq:mufacts]: the archimedean density $\mu(\tau) = \frac{1}{2\pi}\operatorname{Re}\psi(\tfrac14 + \tfrac{i\tau}{2}) - \frac{\log \pi}{2\pi}$ satisfies $\mu(-\tau) = \mu(\tau)$ because negating $\tau$ conjugates the argument of $\psi$. It is consumed by `Zeta23.mu_even`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts.lean#L44-L57

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

open Complex
open scoped ContDiff

theorem Zeta23.digamma_conj (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by sorry
