-- Prove2me | Theorems.Thm_Zeta23_mu_even
-- name    : Zeta23.mu_even
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:55:32.205701+00:00
-- url     : https://prove2.me/theorems/aefe5748-d059-48c6-b2e3-151b10c194ef
-- title:
--   $\mu$ is even: $\mu(-\tau) = \mu(\tau)$
-- statement:
--   Here $\mu$ is the archimedean density of [eq:mudef]:
--   $$\mu(\tau) \;=\; \frac{1}{2\pi}\, \operatorname{Re}\, \frac{\Gamma'}{\Gamma}\Big(\frac14 + \frac{i\tau}{2}\Big) \;-\; \frac{\log \pi}{2\pi},$$
--   with $\Gamma'/\Gamma$ rendered by Mathlib's `Complex.digamma`. The assertion is the evenness clause of [eq:mufacts]:
--   $$\mu(-\tau) \;=\; \mu(\tau) \quad \text{for all } \tau \in \mathbb{R}.$$
--   The proof observes that negating $\tau$ conjugates the argument $\tfrac14 + \tfrac{i\tau}{2}$ and applies the conjugation symmetry of the digamma function (`Zeta23.digamma_conj`), under which the real part is unchanged.
--
--   $\mu$ enters the explicit formula as the density of the archimedean term, and its symmetry is used throughout the prime-side estimates. This lemma (module `Zeta23.GammaFacts`) is consumed by `Zeta23.MuFields.mu_zero_le` and by the headline assemblies `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts.lean#L59-L67, docstring tag [eq:mufacts]

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
import Definitions.Def_Zeta23_Defs

open Zeta23
open Complex
open scoped ContDiff

theorem Zeta23.mu_even (τ : ℝ) : mu (-τ) = mu τ := by sorry
