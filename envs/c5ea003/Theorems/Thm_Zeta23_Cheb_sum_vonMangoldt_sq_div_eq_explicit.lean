-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_div_eq_explicit
-- name    : Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:57.605807+00:00
-- url     : https://prove2.me/theorems/ca843148-fec1-426e-8f2a-3e3e27565397
-- title:
--   Mertens-type asymptotic $\sum_{n\le x}\Lambda(n)^2/n=\tfrac{1}{2}\log^2 x+O(\log x)$ with explicit constant
-- statement:
--   Let $\Lambda$ be the von Mangoldt function and let the sum run over the integers $0<n\le\lfloor x\rfloor$. For every real $x\ge 2$,
--   $$\Bigl|\sum_{0<n\le\lfloor x\rfloor}\frac{\Lambda(n)^2}{n}\;-\;\frac{\log^2 x}{2}\Bigr|\;\le\;C_{2a}\,\log x,\qquad C_{2a}:=2(\log 4+4)+\frac{1537}{\log 2}$$
--   (numerically $C_{2a}\le 2230$).
--
--   This is the first bound of [eq:cheb2] with the implied constant made explicit. In the project it is consumed by `Zeta23.Cheb.chebyshevMertens` (the Chebyshev–Mertens hypothesis bundle H-Cheb) and by `Zeta23.Cheb.sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit`, the weighted companion estimate; together these give the second-moment prime sums entering the mollified moment computation.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L997-L1033, docstring tag [eq:cheb2].1

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

theorem Zeta23.Cheb.sum_vonMangoldt_sq_div_eq_explicit : ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n) - Real.log x ^ 2 / 2|
      ≤ (2 * (Real.log 4 + 4) + 1537 / Real.log 2) * Real.log x := by sorry
