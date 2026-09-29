-- Prove2me | Theorems.Thm_waiting_time_survival_integrable
-- name    : waiting_time_survival_integrable
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T21:55:42.505153+00:00
-- url     : https://prove2.me/theorems/cffd1c6c-3d5a-429c-97ff-33d05039684d
-- title:
--   Integrability of the waiting-time survival function
-- statement:
--   **Integrability of the survival function of the waiting-time CDF.** The lower partial sum $\sum_{k=0}^{m_p}\binom Nk(1-e^{-\lambda t})^k(e^{-\lambda t})^{N-k}$, which equals the survival function $1-F(t)$ of the waiting-time CDF, is integrable on $(0,\infty)$ ($m_p<N$, $\lambda>0$). Each summand is exponentially dominated; the finite sum is integrable. Source: Siegel (2001), Thm 2.2.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals
open MeasureTheory Set Filter Topology Finset
open scoped BigOperators

theorem waiting_time_survival_integrable (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn
      (fun t => ∑ k ∈ Finset.range (mp+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k))
      (Set.Ioi (0:ℝ)) := by sorry
