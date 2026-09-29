-- Prove2me | Theorems.Thm_Zeta23_DigammaSeries_summable_digamma_series
-- name    : Zeta23.DigammaSeries.summable_digamma_series
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:05.609987+00:00
-- url     : https://prove2.me/theorems/705498f0-e6ff-476f-a1a7-957d2cd72e04
-- title:
--   Summability of the digamma partial-fraction series $\sum_{n}\bigl(\tfrac{1}{n+1}-\tfrac{1}{z+n+1}\bigr)$
-- statement:
--   For every $z\in\mathbb{C}$ that is not an integer, the sequence
--   $$n\;\longmapsto\;\frac{1}{n+1}-\frac{1}{z+n+1}\qquad(n\in\mathbb{N})$$
--   is summable (absolutely/unconditionally, in the sense of Mathlib's `Summable`). Indeed the $n$-th term equals $z/((n+1)(z+n+1))=O(n^{-2})$.
--
--   This summability statement accompanies the identification of the sum as $\psi(z)+\gamma+1/z$. It is consumed by `Zeta23.DigammaSeries.hasSum_digamma_series` itself and, downstream, by `Zeta23.MuFields.re_digamma_mono` and `Zeta23.MuFields.re_digamma_vertical`, which derive monotonicity and vertical-line estimates for the real part of the digamma function — ingredients of the Stirling-type facts (H-$\Gamma$) about the archimedean density $\mu$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean#L297-L344

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

theorem Zeta23.DigammaSeries.summable_digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by sorry
