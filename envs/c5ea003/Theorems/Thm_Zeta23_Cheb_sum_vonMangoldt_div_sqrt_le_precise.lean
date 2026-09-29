-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_le_precise
-- name    : Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_precise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:42:46.820314+00:00
-- url     : https://prove2.me/theorems/009819ff-930b-47da-9dba-d54997b320a4
-- title:
--   Partial-summation bound for $\sum_{n \le x} \Lambda(n)/\sqrt{n}$ with explicit lower-order terms
-- statement:
--   Let $\Lambda$ be the von Mangoldt function. For every real $x \ge 1$,
--   $$\sum_{0 < n \le \lfloor x \rfloor} \frac{\Lambda(n)}{\sqrt{n}} \;\le\; 2\log 4 \cdot \sqrt{x} \;+\; 2\log x \;+\; \frac{(\log x)^2}{2},$$
--   where the sum runs over the integers $n \in (0, \lfloor x\rfloor_+]$.
--
--   This is Abel (partial) summation applied to the Chebyshev bound $\psi(t) = \sum_{n \le t} \Lambda(n) \le (\log 4)\, t + \log t$ carried out with explicit constants: the main term $2\log 4 \cdot \sqrt x$ comes from $\int_1^x t^{-1/2}\,d\psi(t)$ against the linear part, and the two logarithmic terms from the $\log t$ correction. Everything is effective — no implied constants.
--
--   It is the source of both all-$x$ Chebyshev bounds used downstream: `sum_vonMangoldt_div_sqrt_le` (constant $2\log 4 + 16$, valid for $x \ge 1$) and `sum_vonMangoldt_div_sqrt_le_three_explicit` (the paper's constant $3$ beyond an explicit threshold), which instantiate field cheb1b of the Chebyshev–Mertens package H-cheb.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L231-L253

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime

theorem Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_precise {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n
      ≤ 2 * Real.log 4 * Real.sqrt x + 2 * Real.log x + Real.log x ^ 2 / 2 := by sorry
