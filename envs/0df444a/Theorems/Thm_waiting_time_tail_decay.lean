-- Prove2me | Theorems.Thm_waiting_time_tail_decay
-- name    : waiting_time_tail_decay
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T21:55:36.292158+00:00
-- url     : https://prove2.me/theorems/c8122852-6838-41ec-a67c-4d6ea033566d
-- title:
--   Exponential tail decay of the waiting-time CDF
-- statement:
--   **Tail-decay (boundary vanishing) of the waiting-time CDF.** For the waiting-time CDF $F(t)=\sum_{k=m_p+1}^{N}\binom Nk(1-e^{-\lambda t})^k(e^{-\lambda t})^{N-k}$ ($m_p<N$, $\lambda>0$), the survival function $1-F(t)$ decays exponentially, so $t\,(1-F(t))\to 0$ as $t\to\infty$. This is the boundary term needed for the integration-by-parts mean identity $\mathbb E[T]=\int_0^\infty(1-F)$. Source: Siegel (2001), Thm 2.2; standard exponential tail estimate.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals
open MeasureTheory Set Filter Topology Finset
open scoped BigOperators

theorem waiting_time_tail_decay (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    Filter.Tendsto (fun t => t * (1 -
      ∑ k ∈ Finset.Ico (mp+1) (N+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)))
      Filter.atTop (nhds 0) := by sorry
