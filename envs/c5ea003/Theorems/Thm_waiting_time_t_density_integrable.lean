-- Prove2me | Theorems.Thm_waiting_time_t_density_integrable
-- name    : waiting_time_t_density_integrable
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T21:55:29.774953+00:00
-- url     : https://prove2.me/theorems/9bd42d88-eaea-4069-be37-b2551ce6768d
-- title:
--   Integrability of $t\,f(t)$ for the waiting-time density
-- statement:
--   **Integrability of the first-moment integrand of the waiting-time density.** Let $f(t)=N\binom{N-1}{m_p}(1-e^{-\lambda t})^{m_p}(e^{-\lambda t})^{N-m_p}\lambda$ be the density of the order-statistic waiting time $T$ (the time the $(m_p{+}1)$-th of $N$ independent rate-$\lambda$ exponential clocks fires), with $m_p<N$, $\lambda>0$. Then $t\mapsto t\,f(t)$ is integrable on $(0,\infty)$ (so $\mathbb E[T]<\infty$). Source: standard exponential-tail domination; used in Siegel, *Median Bounds and their Application*, J. Algorithms 38 (2001), Thm 2.2 (the homogeneous waiting-time model).

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals
open MeasureTheory Set Filter Topology Finset
open scoped BigOperators

theorem waiting_time_t_density_integrable (N mp : ℕ) (lam : ℝ) (h : mp < N) (hlam : 0 < lam) :
    MeasureTheory.IntegrableOn (fun t =>
      t * ((N : ℝ) * (Nat.choose (N-1) mp : ℝ) * (1 - Real.exp (-(lam * t))) ^ mp
        * (Real.exp (-(lam * t))) ^ (N - mp) * lam)) (Set.Ioi (0:ℝ)) := by sorry
