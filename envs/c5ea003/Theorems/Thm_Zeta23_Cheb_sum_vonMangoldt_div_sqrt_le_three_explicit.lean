-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_le_three_explicit
-- name    : Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_three_explicit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:42:53.294363+00:00
-- url     : https://prove2.me/theorems/4125aab7-364d-4135-8e96-3adbf96ee724
-- title:
--   Effective Chebyshev bound $\sum_{n\le x}\Lambda(n)/\sqrt{n}\le 3\sqrt{x}$ with explicit threshold
-- statement:
--   Let $\Lambda$ denote the von Mangoldt function ($\Lambda(n)=\log p$ when $n=p^k$ is a prime power, and $0$ otherwise), and for a real $x$ let the sum below run over the integers $0<n\le\lfloor x\rfloor$.
--
--   For every real $x$ with
--   $$x \;\ge\; \max\Bigl(1,\ \Bigl(\tfrac{48}{3-2\log 4}\Bigr)^{4}\Bigr)$$
--   (an explicit threshold, numerically at most $2.0\cdot 10^{9}$), one has
--   $$\sum_{0<n\le\lfloor x\rfloor}\frac{\Lambda(n)}{\sqrt{n}}\;\le\;3\sqrt{x}.$$
--
--   This is the effective form of the second bound of [eq:cheb1]: it exhibits an explicit witness for the threshold $x_0$ in the paper's statement "$\sum_{n\le x}\Lambda(n)/\sqrt n\le 3\sqrt x$ for $x\ge x_0$". In the project it feeds `Zeta23.Cheb.chebyshevMertens`, the verification of the Chebyshev–Mertens hypothesis bundle (H-Cheb) used by the mollified second-moment argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L275-L322, docstring tag [eq:cheb1].2

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

theorem Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_three_explicit {x : ℝ}
    (hx : max 1 ((48 / (3 - 2 * Real.log 4)) ^ 4) ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x := by sorry
