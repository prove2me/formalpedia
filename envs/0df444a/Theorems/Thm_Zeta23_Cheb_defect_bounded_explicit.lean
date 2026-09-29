-- Prove2me | Theorems.Thm_Zeta23_Cheb_defect_bounded_explicit
-- name    : Zeta23.Cheb.defect_bounded_explicit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:57.367316+00:00
-- url     : https://prove2.me/theorems/95086a46-9c59-4afb-b60b-de5ac26ff5f1
-- title:
--   Explicit bound $\sum_{n \le x} \Lambda(n)(\log n - \Lambda(n))/n \le 1537$
-- statement:
--   Let $\Lambda$ be the von Mangoldt function. For a prime power $n = p^k$ one has $\Lambda(n) = \log p$ while $\log n = k \log p$, so the "defect" $\Lambda(n)(\log n - \Lambda(n))$ is nonzero only at proper prime powers ($k \ge 2$); the defect sum measures how far $\sum \Lambda(n)^2/n$ is from $\sum \Lambda(n)\log n / n$.
--
--   The theorem asserts a fully explicit, uniform bound: for every real $x$,
--   $$\sum_{0 < n \le \lfloor x \rfloor} \frac{\Lambda(n)\,\big(\log n - \Lambda(n)\big)}{n} \;\le\; 1537,$$
--   where the sum runs over the integers $n \in (0, \lfloor x\rfloor_+ ]$ (empty for $x < 1$). The numeral $1537 = 512 \cdot 3 + 1$ comes from bounding the contribution of squares and higher powers by the telescoping estimate $\sum_m m^{-7/4} \le 3$ proved earlier in the file.
--
--   This effective bound is consumed by `sum_vonMangoldt_sq_div_eq_explicit`, which converts the Mertens asymptotic for $\sum \Lambda(n) \log n / n$ into the asymptotic $\sum_{n\le x}\Lambda(n)^2/n = (\log x)^2/2 + O(\log x)$ ([eq:cheb2]) needed by the Chebyshev–Mertens package H-cheb.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L930-L989

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
open MeasureTheory

theorem Zeta23.Cheb.defect_bounded_explicit : ∀ x : ℝ,
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≤ 1537 := by sorry
