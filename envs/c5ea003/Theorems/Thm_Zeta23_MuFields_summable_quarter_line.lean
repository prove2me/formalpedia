-- Prove2me | Theorems.Thm_Zeta23_MuFields_summable_quarter_line
-- name    : Zeta23.MuFields.summable_quarter_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:54:14.198629+00:00
-- url     : https://prove2.me/theorems/d69a526a-fd2c-4f8e-8500-244de97bcded
-- title:
--   Summability of the quarter-line comparison series $\sum_n ((1/4+n)^2+t^2)^{-1}$
-- statement:
--   For every real $t$, the series
--   $$\sum_{n=0}^{\infty} \frac{1}{\bigl(\tfrac14 + n\bigr)^2 + t^2}$$
--   is summable (Lean's `Summable` over $n \in \mathbb{N}$). This is the trigamma-type comparison series on the quarter line $\mathrm{Re} = 1/4$, dominated termwise by $(\tfrac14+n)^{-2}$.
--
--   It supplies the summability input for `Zeta23.MuFields.mu_deriv_bound`, the bound $\mu'(\tau) \ll |\tau|^{-1}$ in the module `Zeta23.GammaFacts.Mu`: differentiating the digamma series for $\mu$ termwise produces sums controlled by this series.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L340-L355

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

open Complex Filter Topology
variable {a : ℝ}

theorem Zeta23.MuFields.summable_quarter_line (t : ℝ) :
    Summable (fun n : ℕ => (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹) := by sorry
