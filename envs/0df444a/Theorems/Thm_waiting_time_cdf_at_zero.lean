-- Prove2me | Theorems.Thm_waiting_time_cdf_at_zero
-- name    : waiting_time_cdf_at_zero
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T22:11:51.990822+00:00
-- url     : https://prove2.me/theorems/96f89f14-9fd8-4d0a-833f-e47da60c8a6b
-- title:
--   The waiting-time CDF vanishes at the origin
-- statement:
--   **The waiting-time CDF vanishes at the origin.** For the order-statistic waiting-time CDF $F(s)=\sum_{k=m_p+1}^{N}\binom Nk(1-e^{-\lambda s})^k(e^{-\lambda s})^{N-k}$ ($m_p<N$), one has $F(0)=0$. At $s=0$, $e^{-\lambda\cdot 0}=1$ so each factor $(1-e^{-\lambda\cdot 0})^k=0^k=0$ for $k\ge m_p+1\ge 1$; hence every summand vanishes. Source: Siegel, *Median Bounds and their Application*, J. Algorithms 38 (2001), Thm 2.2.

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Exp
open scoped BigOperators
open Finset

theorem waiting_time_cdf_at_zero (N mp : ℕ) (lam : ℝ) (h : mp < N) :
    (∑ k ∈ Finset.Ico (mp+1) (N+1),
      (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * (0:ℝ)))) ^ k
        * (Real.exp (-(lam * (0:ℝ)))) ^ (N - k)) = 0 := by sorry
