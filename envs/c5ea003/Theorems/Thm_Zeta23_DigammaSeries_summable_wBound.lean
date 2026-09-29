-- Prove2me | Theorems.Thm_Zeta23_DigammaSeries_summable_wBound
-- name    : Zeta23.DigammaSeries.summable_wBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:44:40.076598+00:00
-- url     : https://prove2.me/theorems/c77b7ab0-4819-4329-9508-3e8d4c2b6335
-- title:
--   Summability of the dominating sequence $3\,(R/(n+1))^2$
-- statement:
--   For every real $R$, the sequence
--   $$n\;\longmapsto\;3\Bigl(\frac{R}{n+1}\Bigr)^{2}\qquad(n\in\mathbb{N})$$
--   is summable — a rescaling of the convergent series $\sum_n (n+1)^{-2}$.
--
--   This is the summable majorant matching the quadratic Weierstrass-factor bound `norm_wTerm_le` ($\|w_n(z)\|\le 3(\|z\|/(n+1))^2$ for $\|z\|\le n+1$): with $R=\|z\|$ it dominates the tail of the Weierstrass product and of the digamma series. It is consumed by `Zeta23.DigammaSeries.inv_gamma_eq_prod` and `Zeta23.DigammaSeries.hasSum_digamma_series` in the GammaFacts part of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean#L89-L105

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

theorem Zeta23.DigammaSeries.summable_wBound (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by sorry
