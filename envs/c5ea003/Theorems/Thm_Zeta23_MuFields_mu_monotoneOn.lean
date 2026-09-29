-- Prove2me | Theorems.Thm_Zeta23_MuFields_mu_monotoneOn
-- name    : Zeta23.MuFields.mu_monotoneOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:55:27.054711+00:00
-- url     : https://prove2.me/theorems/fbe1a450-e1f8-424d-abcd-562f85cdd1b4
-- title:
--   Monotonicity of $\mu$ on $[0,\infty)$
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], $\mu(\tau) = \frac{1}{2\pi}\mathrm{Re}\,\frac{\Gamma'}{\Gamma}(\tfrac14 + \tfrac{i\tau}{2}) - \frac{\log\pi}{2\pi}$. The theorem formalizes the clause "increasing in $|\tau|$" of [eq:mufacts]:
--   $$\mu \text{ is monotone (non-decreasing) on } [0,\infty),$$
--   stated as `MonotoneOn Zeta23.mu (Set.Ici 0)`. Combined with the evenness of $\mu$, this gives monotonicity in $|\tau|$.
--
--   Within `Zeta23.GammaFacts.Mu` it follows from the monotonicity of $t \mapsto \mathrm{Re}\,\psi(a+it)$ on vertical lines; it feeds the lower bound `Zeta23.MuFields.mu_zero_le` and the assembly theorems `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L139-L150, docstring tag [eq:mufacts]

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

theorem Zeta23.MuFields.mu_monotoneOn : MonotoneOn Zeta23.mu (Set.Ici (0 : ℝ)) := by sorry
