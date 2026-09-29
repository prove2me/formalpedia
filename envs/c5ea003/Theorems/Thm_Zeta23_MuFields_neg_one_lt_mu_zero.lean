-- Prove2me | Theorems.Thm_Zeta23_MuFields_neg_one_lt_mu_zero
-- name    : Zeta23.MuFields.neg_one_lt_mu_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:17.425285+00:00
-- url     : https://prove2.me/theorems/a11e1302-cc5b-498c-826a-f9b634568c63
-- title:
--   Strict lower bound $\mu(0) > -1$
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], so that
--   $$\mu(0) \;=\; \frac{1}{2\pi}\,\frac{\Gamma'}{\Gamma}\Bigl(\frac14\Bigr) \;-\; \frac{\log\pi}{2\pi}.$$
--   The theorem is the numerical clause "$\mu(0) > -1$" of [eq:mufacts]:
--   $$-1 \;<\; \mu(0).$$
--   The proof evaluates $\mathrm{Re}\,\psi(1/4)$ through the digamma series representation on vertical lines (`Zeta23.MuFields.re_digamma_vertical`) and elementary estimates.
--
--   Together with $\mu \ge \mu(0)$ this gives the uniform lower bound $\mu > -1$ used by the assembly theorems `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L161-L210, docstring tag [eq:mufacts]

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

theorem Zeta23.MuFields.neg_one_lt_mu_zero : (-1 : ℝ) < Zeta23.mu 0 := by sorry
