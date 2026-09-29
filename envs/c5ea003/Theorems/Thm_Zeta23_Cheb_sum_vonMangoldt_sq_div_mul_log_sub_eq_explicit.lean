-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit
-- name    : Zeta23.Cheb.sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:44:14.0223+00:00
-- url     : https://prove2.me/theorems/06881859-72f0-48d7-a630-0efc467c3c7e
-- title:
--   Weighted Mertens-type asymptotic $\sum_{n\le x}\frac{\Lambda(n)^2}{n}(\log x-\log n)=\tfrac{1}{6}\log^3 x+O(\log^2 x)$
-- statement:
--   Let $\Lambda$ be the von Mangoldt function and let the sum run over the integers $0<n\le\lfloor x\rfloor$. For every real $x\ge 2$,
--   $$\Bigl|\sum_{0<n\le\lfloor x\rfloor}\frac{\Lambda(n)^2}{n}\bigl(\log x-\log n\bigr)\;-\;\frac{\log^3 x}{6}\Bigr|\;\le\;C_{2b}\,\log^2 x,$$
--   where the constant is explicit:
--   $$C_{2b}:=\frac{C_{2a}}{2}+\frac{1}{\log 2},\qquad C_{2a}=2(\log 4+4)+\frac{1537}{\log 2}.$$
--
--   This is the second bound of [eq:cheb2] with the implied constant made explicit; it follows from the unweighted version (`Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit`) by partial summation. It is consumed by `Zeta23.Cheb.chebyshevMertens`, the verification of the Chebyshev–Mertens hypothesis bundle (H-Cheb) feeding the mollified second-moment argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L1046-L1180, docstring tag [eq:cheb2].2

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

theorem Zeta23.Cheb.sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit : ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)) -
        Real.log x ^ 3 / 6|
      ≤ ((2 * (Real.log 4 + 4) + 1537 / Real.log 2) / 2 + 1 / Real.log 2) * Real.log x ^ 2 := by sorry
