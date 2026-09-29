-- Prove2me | Theorems.Thm_Zeta23_mu_smooth
-- name    : Zeta23.mu_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:33.807443+00:00
-- url     : https://prove2.me/theorems/7e18b62f-db95-40db-b400-fa18df72a826
-- title:
--   $\mu$ is smooth: $\mu \in C^\infty(\mathbb{R})$
-- statement:
--   With $\mu(\tau) = \frac{1}{2\pi}\operatorname{Re}\,\frac{\Gamma'}{\Gamma}(\tfrac14 + \tfrac{i\tau}{2}) - \frac{\log\pi}{2\pi}$ the archimedean density of [eq:mudef], the assertion is the smoothness clause of [eq:mufacts]: $\mu$ is infinitely differentiable on $\mathbb{R}$, formalized as
--   $$\mathrm{ContDiff}\; \mathbb{R}\; \infty\; \mu.$$
--   The proof shows the complex digamma function is analytic on the right half-plane $\operatorname{Re} z > 0$ (since $\Gamma$ is holomorphic and nonvanishing there), restricts scalars to $\mathbb{R}$, and composes with the affine map $\tau \mapsto \tfrac14 + \tfrac{i\tau}{2}$, whose image stays in the half-plane.
--
--   Smoothness of $\mu$ is needed wherever $\mu$ is integrated against test data on the prime side — in particular for the moment integrals [eq:muints]. This lemma (module `Zeta23.GammaFacts`) is consumed by `Zeta23.MuInts.int_mu_of_stirling`, `Zeta23.MuInts.int_mu_sq_of_stirling`, and the headline assemblies `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts.lean#L94-L119, docstring tag [eq:mufacts]

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
set_option backward.isDefEq.respectTransparency false

theorem Zeta23.mu_smooth : ContDiff ℝ ∞ mu := by sorry
