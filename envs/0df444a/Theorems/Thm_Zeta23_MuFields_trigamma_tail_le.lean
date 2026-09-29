-- Prove2me | Theorems.Thm_Zeta23_MuFields_trigamma_tail_le
-- name    : Zeta23.MuFields.trigamma_tail_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:54:15.414396+00:00
-- url     : https://prove2.me/theorems/c340da63-dc56-4b87-91c5-c01eaa31f59b
-- title:
--   Trigamma tail bound $\sum_n ((1/4+n)^2+t^2)^{-1} \le 12/|t|$
-- statement:
--   For every real $t$ with $|t| \ge 1/2$, the quarter-line trigamma comparison series satisfies
--   $$\sum_{n=0}^{\infty} \frac{1}{\bigl(\tfrac14 + n\bigr)^2 + t^2} \;\le\; \frac{12}{|t|},$$
--   where the sum is a `tsum` over $n \in \mathbb{N}$. The proof compares the sum with the integral $\int_0^\infty \frac{dx}{x^2+t^2} = \frac{\pi}{2|t|}$, with explicit constants.
--
--   Together with `Zeta23.MuFields.summable_quarter_line`, this quantitative tail bound is what turns the termwise-differentiated digamma series into the derivative estimate `Zeta23.MuFields.mu_deriv_bound` ($\mu'(\tau) \ll |\tau|^{-1}$) in the module `Zeta23.GammaFacts.Mu`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/Mu.lean#L214-L338

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

theorem Zeta23.MuFields.trigamma_tail_le {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + t ^ 2)⁻¹ ≤ 12 / |t| := by sorry
