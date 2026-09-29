-- Prove2me | Theorems.Thm_Zeta23_Cheb_rpow_inv_le_telescope
-- name    : Zeta23.Cheb.rpow_inv_le_telescope
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:43:47.920337+00:00
-- url     : https://prove2.me/theorems/d008699f-aa9d-4e31-9a9a-0b72120cb47b
-- title:
--   Telescoping bound $m^{-7/4} \le 2\big(1/\sqrt{m-1} - 1/\sqrt{m}\,\big)$
-- statement:
--   For every natural number $m \ge 2$ (viewed as a real number, with the real power $m^{7/4}$),
--   $$\frac{1}{m^{7/4}} \;\le\; 2\left(\frac{1}{\sqrt{m-1}} - \frac{1}{\sqrt{m}}\right).$$
--
--   This is the standard comparison behind bounding $\sum_m m^{-7/4}$ by a telescoping sum: the mean value theorem heuristic $1/\sqrt{m-1} - 1/\sqrt m \approx \tfrac12 m^{-3/2} \ge \tfrac12 m^{-7/4}$, made into an exact elementary inequality.
--
--   It is the single step consumed by `sum_range_rpow_inv_le`, which telescopes it into the partial-sum bound $\sum_{m \le N} m^{-7/4} \le 3 - 2/\sqrt N$; that in turn feeds the explicit constant in the defect bound `defect_bounded_explicit` of the Chebyshev–Mertens chapter.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L836-L882

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

theorem Zeta23.Cheb.rpow_inv_le_telescope {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 2 * (1 / Real.sqrt (m - 1) - 1 / Real.sqrt m) := by sorry
