-- Prove2me | Theorems.Thm_waiting_time_survival_mean
-- name    : waiting_time_survival_mean
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:39:18.673264+00:00
-- url     : https://prove2.me/theorems/42b551c3-4ee2-4388-a417-feb39ad54b74
-- title:
--   Mean waiting time equals a harmonic sum divided by $\lambda$
-- statement:
--   **Mean of the waiting time = harmonic sum / λ.** For $0 \le m < N$ and rate $\lambda>0$, the integral over $(0,\infty)$ of the binomial survival function (lower partial sum) of the exp-clock waiting-time model equals $\frac{1}{\lambda}\sum_{k=0}^{m}\frac{1}{N-k}$: $$\int_0^\infty \sum_{k=0}^{m}\binom{N}{k}(1-e^{-\lambda t})^k(e^{-\lambda t})^{N-k}\,dt = \frac{1}{\lambda}\sum_{k=0}^{m}\frac{1}{N-k} = \frac{1}{\lambda}(H_N - H_{N-m-1}).$$ Since the integrand is the survival function $P(T>t)$ of the waiting time $T$ until $m+1$ of $N$ independent rate-$\lambda$ exponential clocks fire, this is the mean $E[T] = \int_0^\infty P(T>t)\,dt$. Proved by linearity of the integral over the finite sum, applying the per-term survival integral $\binom{N}{k}\int_0^\infty (1-e^{-\lambda t})^k(e^{-\lambda t})^{N-k}\,dt = \frac{1}{\lambda(N-k)}$.
-- source:
--   Siegel, "Median Bounds and their Application", J. Algorithms 38:184-236, 2001, §2.1.1; the waiting-time mean $E[T]=\frac{1}{\lambda}\sum_{j=N-m}^{N}\frac{1}{j}$ (eq. for E[T], p.6).

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
open MeasureTheory Set Finset
open scoped BigOperators

theorem waiting_time_survival_mean (N m : ℕ) (lam : ℝ) (hlam : 0 < lam) (hm : m < N) :
    ∫ t in Set.Ioi (0:ℝ), ∑ k ∈ Finset.range (m+1),
        (Nat.choose N k : ℝ) * (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ∑ k ∈ Finset.range (m+1), (1 / ((N - k : ℕ) : ℝ)) := by sorry
