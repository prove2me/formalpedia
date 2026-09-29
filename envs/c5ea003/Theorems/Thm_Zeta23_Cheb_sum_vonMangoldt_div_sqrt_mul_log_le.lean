-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_mul_log_le
-- name    : Zeta23.Cheb.sum_vonMangoldt_div_sqrt_mul_log_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:37.179498+00:00
-- url     : https://prove2.me/theorems/60a24426-9666-4762-9b76-a4a675075e26
-- title:
--   Chebyshev-type bound $\sum_{n\le x}\Lambda(n)/(\sqrt{n}\log n)\le C\sqrt{x}/\log x$
-- statement:
--   Let $\Lambda$ be the von Mangoldt function and let the sum run over the integers $0<n\le\lfloor x\rfloor$. For every real $x\ge 2$,
--   $$\sum_{0<n\le\lfloor x\rfloor}\frac{\Lambda(n)}{\sqrt{n}\,\log n}\;\le\;(4\log 4+40)\,\frac{\sqrt{x}}{\log x}.$$
--
--   The $n=1$ summand is harmless in the Lean statement: $\Lambda(1)=0$ (and Lean's convention $0/0=0$ makes the term with denominator $\sqrt{1}\cdot\log 1=0$ equal to $0$), so the sum effectively starts at $n=2$. The constant $4\log 4+40$ is explicit.
--
--   This is the third bound of [eq:cheb1]. It is consumed by `Zeta23.Cheb.chebyshevMertens`, the verification of the Chebyshev–Mertens hypothesis bundle (H-Cheb) that supplies the elementary prime-sum estimates for the mollified second-moment computation.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L351-L469, docstring tag [eq:cheb1].3

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

theorem Zeta23.Cheb.sum_vonMangoldt_div_sqrt_mul_log_le {x : ℝ} (hx : 2 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤
      (4 * Real.log 4 + 40) * Real.sqrt x / Real.log x := by sorry
