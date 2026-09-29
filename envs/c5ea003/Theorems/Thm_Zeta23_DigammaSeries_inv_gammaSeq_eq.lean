-- Prove2me | Theorems.Thm_Zeta23_DigammaSeries_inv_gammaSeq_eq
-- name    : Zeta23.DigammaSeries.inv_gammaSeq_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:44:29.565139+00:00
-- url     : https://prove2.me/theorems/2a07af19-b91c-4d16-9b1b-5a348a50c129
-- title:
--   Finite Weierstrass identity for the reciprocal Euler–Gauss sequence $(\mathrm{GammaSeq}\,z\,N)^{-1}$
-- statement:
--   Let $\mathrm{GammaSeq}\,z\,N = N^z N!/(z(z+1)\cdots(z+N))$ be Mathlib's Euler–Gauss approximating sequence for $\Gamma(z)$, let $H_N=\sum_{m=0}^{N-1}\frac{1}{m+1}$ be the $N$-th harmonic number, and let
--   $$w_n(z)\;:=\;\Bigl(1+\frac{z}{n+1}\Bigr)e^{-z/(n+1)}-1$$
--   be the (shifted) Weierstrass factor (`wTerm`). Then for every $z$ in the integer complement (a hypothesis carried by the statement) and every $N\ge 1$,
--   $$\bigl(\mathrm{GammaSeq}\,z\,N\bigr)^{-1}\;=\;z\,e^{(H_N-\log N)\,z}\prod_{n=0}^{N-1}\bigl(1+w_n(z)\bigr).$$
--
--   This finite algebraic identity is the pre-limit form of the Weierstrass product for $1/\Gamma$: letting $N\to\infty$ (using $H_N-\log N\to\gamma$) yields the infinite product. It is consumed by `Zeta23.DigammaSeries.inv_gamma_eq_prod` in the GammaFacts part of the project, which underpins the digamma series used for the archimedean density in the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean#L129-L205

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

theorem Zeta23.DigammaSeries.inv_gammaSeq_eq {z : ℂ} (_hz : z ∈ Complex.integerComplement) {N : ℕ} (hN : 1 ≤ N) :
    (Complex.GammaSeq z N)⁻¹
      = z * Complex.exp ((((∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1))
            - Real.log N : ℝ) : ℂ) * z)
          * ∏ n ∈ Finset.range N, (1 + wTerm n z) := by sorry
