-- Prove2me | Theorems.Thm_Zeta23_DigammaSeries_inv_gamma_eq_prod
-- name    : Zeta23.DigammaSeries.inv_gamma_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:44:45.6287+00:00
-- url     : https://prove2.me/theorems/5624cc93-3324-4a8c-8794-db9561e5b666
-- title:
--   Weierstrass product $\Gamma(z)^{-1}=z\,e^{\gamma z}\prod_{n\ge 0}(1+\tfrac{z}{n+1})e^{-z/(n+1)}$
-- statement:
--   Let $\Gamma$ be the complex Gamma function, $\gamma$ the Euler–Mascheroni constant, and
--   $$w_n(z)\;:=\;\Bigl(1+\frac{z}{n+1}\Bigr)e^{-z/(n+1)}-1$$
--   the Weierstrass factor (`wTerm`), so that $1+w_n(z)=(1+\frac{z}{n+1})e^{-z/(n+1)}$. For every $z\in\mathbb{C}$ that is not an integer,
--   $$\Gamma(z)^{-1}\;=\;z\,e^{\gamma z}\prod_{n=0}^{\infty}\bigl(1+w_n(z)\bigr),$$
--   the product being a `tprod` over $n\in\mathbb{N}$.
--
--   This is the classical Weierstrass product for $1/\Gamma$, obtained from the finite identity for the Euler–Gauss sequence (`inv_gammaSeq_eq`) by passing to the limit with the quadratic tail bound `norm_wTerm_le`. It is consumed by `Zeta23.DigammaSeries.hasSum_digamma_series`, whose termwise logarithmic differentiation produces the digamma partial-fraction series used for the archimedean density $\mu$ in the explicit-formula part of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Series.lean#L207-L246

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

theorem Zeta23.DigammaSeries.inv_gamma_eq_prod {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (Complex.Gamma z)⁻¹
      = z * Complex.exp ((Real.eulerMascheroniConstant : ℂ) * z)
          * ∏' n : ℕ, (1 + wTerm n z) := by sorry
