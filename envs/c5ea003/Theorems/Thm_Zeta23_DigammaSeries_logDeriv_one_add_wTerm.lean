-- Prove2me | Theorems.Thm_Zeta23_DigammaSeries_logDeriv_one_add_wTerm
-- name    : Zeta23.DigammaSeries.logDeriv_one_add_wTerm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:44:50.340073+00:00
-- url     : https://prove2.me/theorems/cfe66b42-fe70-4657-8883-8c3d54fba4bb
-- title:
--   Logarithmic derivative of a Weierstrass factor: $\frac{d}{dz}\log\bigl[(1+\tfrac{z}{n+1})e^{-z/(n+1)}\bigr]=\tfrac{1}{z+n+1}-\tfrac{1}{n+1}$
-- statement:
--   Let $w_n(z):=(1+\frac{z}{n+1})e^{-z/(n+1)}-1$ be the Weierstrass factor (`wTerm`), and let $\operatorname{logDeriv} f = f'/f$ denote Mathlib's logarithmic derivative. For every $z\in\mathbb{C}$ that is not an integer and every $n\in\mathbb{N}$,
--   $$\operatorname{logDeriv}\bigl(s\mapsto 1+w_n(s)\bigr)(z)\;=\;\frac{1}{z+n+1}-\frac{1}{n+1}.$$
--
--   Note the sign convention: the summands of the digamma series are the negatives of these values. This is the single-factor computation behind the termwise logarithmic differentiation of the Weierstrass product for $1/\Gamma$; it is consumed by `Zeta23.DigammaSeries.hasSum_digamma_series`, which assembles the digamma partial-fraction series feeding the archimedean (Gamma-factor) analysis of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean#L248-L295

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

theorem Zeta23.DigammaSeries.logDeriv_one_add_wTerm {z : ℂ} (hz : z ∈ Complex.integerComplement) (n : ℕ) :
    logDeriv (fun s => 1 + wTerm n s) z = 1 / (z + n + 1) - 1 / ((n : ℂ) + 1) := by sorry
