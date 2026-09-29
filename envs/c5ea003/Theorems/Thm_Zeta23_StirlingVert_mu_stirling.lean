-- Prove2me | Theorems.Thm_Zeta23_StirlingVert_mu_stirling
-- name    : Zeta23.StirlingVert.mu_stirling
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:00.152863+00:00
-- url     : https://prove2.me/theorems/4d635c26-b1f2-4adc-b922-b347570624f8
-- title:
--   Stirling clause of H-$\Gamma$: $\mu(\tau) = \frac{1}{2\pi}\log\frac{|\tau|}{2\pi} + O(\tau^{-2})$
-- statement:
--   Let $\mu$ be the archimedean density of the project (`Zeta23.mu`):
--   $$\mu(\tau) \;=\; \frac{1}{2\pi}\,\operatorname{Re}\,\psi\Bigl(\frac14 + \frac{i\tau}{2}\Bigr) \;-\; \frac{\log\pi}{2\pi},$$
--   with $\psi = \Gamma'/\Gamma$ the digamma function.
--
--   **Statement.** There exists a constant $C$ such that for every real $\tau$ with $|\tau| \ge 1$,
--   $$\Bigl|\,\mu(\tau) \;-\; \frac{1}{2\pi}\,\log\frac{|\tau|}{2\pi}\,\Bigr| \;\le\; \frac{C}{\tau^{2}}$$
--   (the proof furnishes $C = 20/(2\pi) \le 4$).
--
--   This is exactly the Stirling clause of the hypothesis bundle H-$\Gamma$ [eq:mufacts], in the shape of the field `Zeta23.GammaFacts.stirling`; it is the statement that the density of zeros predicted by the archimedean factor grows like $\frac{1}{2\pi}\log\frac{\tau}{2\pi}$ with a quadratically decaying error. It is consumed by the headline assemblies `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/StirlingVert.lean#L614-L637, docstring tag [eq:mufacts]

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

theorem Zeta23.StirlingVert.mu_stirling : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2 := by sorry
