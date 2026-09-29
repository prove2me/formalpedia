-- Prove2me | Theorems.Thm_Zeta23_Cheb_tsum_rpow_neg_seven_quarters_le
-- name    : Zeta23.Cheb.tsum_rpow_neg_seven_quarters_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:47.225048+00:00
-- url     : https://prove2.me/theorems/bf79e4e6-6048-493a-8014-21a275e9ab33
-- title:
--   Zeta-value bound $\sum_{m\ge 1} m^{-7/4}\le 3$
-- statement:
--   The series of the powers $m^{-7/4}$ over the natural numbers is bounded by $3$:
--   $$\sum_{m=0}^{\infty}\bigl(m^{7/4}\bigr)^{-1}\;\le\;3.$$
--   In the Lean statement the sum runs over all $m\in\mathbb{N}$ including $m=0$; by Lean's conventions $0^{7/4}=0$ and $0^{-1}=0$, so the $m=0$ term vanishes and the assertion is exactly $\zeta(7/4)=\sum_{m\ge 1}m^{-7/4}\le 3$. (The sum is a `tsum`, which equals the limit since the series converges.)
--
--   This numerical estimate is consumed by `Zeta23.Cheb.defect_bounded_explicit` in the Chebyshev module, where it controls a tail arising from higher prime powers in the comparison between $\psi$-type sums and their main terms.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L914-L928

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

theorem Zeta23.Cheb.tsum_rpow_neg_seven_quarters_le :
    ∑' m : ℕ, ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 3 := by sorry
