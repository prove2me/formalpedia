-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_le
-- name    : Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:37.561788+00:00
-- url     : https://prove2.me/theorems/40dabc0c-a672-4383-b44f-d611831b5669
-- title:
--   Chebyshev bound $\sum_{n \le x} \Lambda(n)/\sqrt{n} \le (2\log 4 + 16)\sqrt{x}$ for all $x \ge 1$
-- statement:
--   Let $\Lambda$ be the von Mangoldt function. For every real $x \ge 1$,
--   $$\sum_{0 < n \le \lfloor x \rfloor} \frac{\Lambda(n)}{\sqrt{n}} \;\le\; \big(2\log 4 + 16\big)\,\sqrt{x},$$
--   where the sum runs over the integers $n \in (0, \lfloor x\rfloor_+]$ (the Mathlib `Chebyshev.psi` indexing).
--
--   This is the second estimate of [eq:cheb1] in an "all-$x$" form: unlike the paper's version $\sum_{n\le x}\Lambda(n)/\sqrt n \le 3\sqrt x$, which holds only for $x \ge x_0$, here the constant $2\log 4 + 16 \approx 18.77$ is worse but the bound is valid from $x = 1$ on with no threshold. It follows from the precise partial-summation bound `sum_vonMangoldt_div_sqrt_le_precise` by absorbing the lower-order terms $2\log x + (\log x)^2/2$ into $16\sqrt x$.
--
--   It is consumed by `sum_vonMangoldt_div_sqrt_mul_log_le` en route to the estimate $\sum_{n \le x} \Lambda(n)/(\sqrt n\, \log n) \ll \sqrt x/\log x$, another field of the Chebyshev–Mertens package H-cheb that feeds the prime side of the proof of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L255-L273, docstring tag [eq:cheb1]

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

theorem Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ (2 * Real.log 4 + 16) * Real.sqrt x := by sorry
