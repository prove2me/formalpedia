-- Prove2me | Theorems.Thm_Zeta23_Cheb_sum_range_rpow_inv_le
-- name    : Zeta23.Cheb.sum_range_rpow_inv_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:47.608521+00:00
-- url     : https://prove2.me/theorems/acafaf80-2d77-47e9-a44e-9c828e1a28bc
-- title:
--   Partial sums $\sum_{m \le N} m^{-7/4} \le 3 - 2/\sqrt{N}$
-- statement:
--   For every natural number $N \ge 1$,
--   $$\sum_{m=0}^{N} \frac{1}{m^{7/4}} \;\le\; 3 - \frac{2}{\sqrt{N}},$$
--   where the sum runs over `Finset.range (N+1)`, i.e. $0 \le m \le N$; the $m = 0$ term is $0$ under Lean's convention $(0^{7/4})^{-1} = 0^{-1} = 0$, and the powers are real powers.
--
--   The proof keeps the $m = 1$ term (equal to $1$) and telescopes the terms $m \ge 2$ via `rpow_inv_le_telescope` ($m^{-7/4} \le 2(1/\sqrt{m-1} - 1/\sqrt m)$), giving $1 + 2(1 - 1/\sqrt N) = 3 - 2/\sqrt N$. The explicit remainder $-2/\sqrt N$ makes the bound usable in an induction and shows the tail control is uniform in $N$.
--
--   It is consumed by `tsum_rpow_neg_seven_quarters_le`, the bound $\sum_{m \ge 1} m^{-7/4} \le 3$ used for the explicit constant $1537$ in the defect bound of the Chebyshev–Mertens chapter (`defect_bounded_explicit`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L884-L912

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

theorem Zeta23.Cheb.sum_range_rpow_inv_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.range (N + 1), ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 3 - 2 / Real.sqrt N := by sorry
