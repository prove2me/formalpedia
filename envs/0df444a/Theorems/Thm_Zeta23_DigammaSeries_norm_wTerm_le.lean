-- Prove2me | Theorems.Thm_Zeta23_DigammaSeries_norm_wTerm_le
-- name    : Zeta23.DigammaSeries.norm_wTerm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:44:34.723863+00:00
-- url     : https://prove2.me/theorems/229de157-1a82-420c-94b3-59b992b6deba
-- title:
--   Quadratic bound for the Weierstrass factor: $\bigl\|(1+\tfrac{z}{n+1})e^{-z/(n+1)}-1\bigr\|\le 3\bigl(\tfrac{\|z\|}{n+1}\bigr)^2$
-- statement:
--   Let $w_n(z):=(1+\frac{z}{n+1})e^{-z/(n+1)}-1$ be the Weierstrass factor (`wTerm`). For every $z\in\mathbb{C}$ and $n\in\mathbb{N}$ with $\|z\|\le n+1$,
--   $$\|w_n(z)\|\;\le\;3\Bigl(\frac{\|z\|}{n+1}\Bigr)^{2}.$$
--
--   This quadratic tail bound expresses that the Weierstrass factors converge to $1$ at rate $O(n^{-2})$ on compact sets, which is exactly what makes the product $\prod_n(1+w_n(z))$ and the associated logarithmic-derivative series absolutely convergent. It is consumed by `Zeta23.DigammaSeries.inv_gamma_eq_prod` (the Weierstrass product for $1/\Gamma$) and `Zeta23.DigammaSeries.hasSum_digamma_series` (the digamma partial-fraction series) in the GammaFacts part of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean#L49-L87

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

theorem Zeta23.DigammaSeries.norm_wTerm_le {z : ℂ} {n : ℕ} (h : ‖z‖ ≤ (n : ℝ) + 1) :
    ‖wTerm n z‖ ≤ 3 * (‖z‖ / ((n : ℝ) + 1)) ^ 2 := by sorry
