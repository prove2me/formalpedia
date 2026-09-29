-- Prove2me | Theorems.Thm_Zeta23_DigammaSeries_hasSum_digamma_series
-- name    : Zeta23.DigammaSeries.hasSum_digamma_series
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:45:59.996015+00:00
-- url     : https://prove2.me/theorems/5f725167-3f7e-435d-b4f4-f727f1a5d5de
-- title:
--   Partial-fraction series for the digamma function $\psi(z)+\gamma+\tfrac1z=\sum_{n\ge 0}\bigl(\tfrac{1}{n+1}-\tfrac{1}{z+n+1}\bigr)$
-- statement:
--   Let $\psi=\Gamma'/\Gamma$ denote the complex digamma function (Mathlib's `Complex.digamma`) and $\gamma$ the Euler–Mascheroni constant. For every $z\in\mathbb{C}$ that is not an integer (i.e. $z$ in the integer complement), the series
--   $$\sum_{n=0}^{\infty}\Bigl(\frac{1}{n+1}-\frac{1}{z+n+1}\Bigr)$$
--   converges (in the unconditional `HasSum` sense) with sum
--   $$\psi(z)+\gamma+\frac{1}{z}.$$
--
--   This is the classical partial-fraction expansion of the digamma function, derived here from the Weierstrass product for $1/\Gamma$ by termwise logarithmic differentiation. In the project it is the gateway from Mathlib's Gamma function to concrete estimates for the archimedean (Gamma-factor) density: it is consumed by `Zeta23.MuFields.re_digamma_vertical`, `Zeta23.Stirling.hasSum_trigamma`, `Zeta23.StirlingVert.digamma_eq`, and `Zeta23.WeilEF.digamma_conj`, which feed the Stirling-type facts (H-$\Gamma$) about the density $\mu$ in the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean#L346-L487

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
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series

open Zeta23
open DigammaSeries
open Complex Filter Topology

theorem Zeta23.DigammaSeries.hasSum_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by sorry
