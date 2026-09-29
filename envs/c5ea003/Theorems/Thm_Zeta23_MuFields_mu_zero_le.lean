-- Prove2me | Theorems.Thm_Zeta23_MuFields_mu_zero_le
-- name    : Zeta23.MuFields.mu_zero_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:12.413196+00:00
-- url     : https://prove2.me/theorems/8ecf0b7c-dcae-483b-be92-1f34b18a82bd
-- title:
--   Global lower bound $\mu(\tau) \ge \mu(0)$
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], $\mu(\tau) = \frac{1}{2\pi}\mathrm{Re}\,\frac{\Gamma'}{\Gamma}(\tfrac14 + \tfrac{i\tau}{2}) - \frac{\log\pi}{2\pi}$. The theorem is the "$\mu \ge \mu(0)$" clause of [eq:mufacts]:
--   $$\mu(0) \;\le\; \mu(\tau) \qquad \text{for every } \tau \in \mathbb{R},$$
--   that is, $\mu$ attains its global minimum at $\tau = 0$. It is deduced from the monotonicity of $\mu$ on $[0,\infty)$ (`Zeta23.MuFields.mu_monotoneOn`) together with the evenness of $\mu$.
--
--   As one of the H-$\Gamma$ fields of `Zeta23.GammaFacts.Mu`, it is consumed by the assembly theorems `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L152-L159, docstring tag [eq:mufacts]

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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs

open Zeta23
open Complex Filter Topology
variable {a : ℝ}

theorem Zeta23.MuFields.mu_zero_le (τ : ℝ) : Zeta23.mu 0 ≤ Zeta23.mu τ := by sorry
