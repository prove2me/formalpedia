-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_one_div_sqrt_le
-- name    : Zeta23.Cheb.sum_one_div_sqrt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:36.77883+00:00
-- url     : https://prove2.me/theorems/e24b1b4e-83b4-4316-8c65-ae75666b55b2
-- title:
--   $\sum_{n \le N} 1/\sqrt{n} \le 2\sqrt{N}$
-- statement:
--   For every natural number $N$,
--   $$\sum_{n=1}^{N} \frac{1}{\sqrt{n}} \;\le\; 2\sqrt{N},$$
--   where the sum in Lean runs over $n \in (0, N]$ (empty for $N = 0$, in which case both sides vanish).
--
--   This is the classical elementary estimate, proved by induction on $N$ using $2\sqrt{N} + 1/\sqrt{N+1} \le 2\sqrt{N+1}$ (equivalently, the telescoping comparison $1/\sqrt{n} \le 2(\sqrt{n} - \sqrt{n-1})$).
--
--   In the Chebyshev chapter it is the partial-summation input consumed by `sum_vonMangoldt_div_sqrt_mul_log_le`, the bound $\sum_{n \le x} \Lambda(n)/(\sqrt n \log n) \ll \sqrt x / \log x$ of [eq:cheb1] in the Chebyshev–Mertens package H-cheb.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L331-L349

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

theorem Zeta23.Cheb.sum_one_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (1 : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt N := by sorry
