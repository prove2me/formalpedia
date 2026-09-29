-- Prove2me | Theorems.Thm_waiting_survival_per_term_integral
-- name    : waiting_survival_per_term_integral
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:34:57.974178+00:00
-- url     : https://prove2.me/theorems/465e9b57-0609-44c0-9616-0b119522bcf2
-- title:
--   Per-term survival integral of the waiting-time model
-- statement:
--   **Per-term survival integral of the waiting-time model.** For $0 \le k < N$ and rate $\lambda>0$, $$\int_0^\infty (1-e^{-\lambda t})^k (e^{-\lambda t})^{N-k}\,dt = \frac{1}{\lambda}\cdot\frac{k!\,(N-k-1)!}{N!}.$$ This is the $k$-th term of the survival function $1-F(t)=\sum_{k=0}^{m}\binom{N}{k}(1-e^{-\lambda t})^k(e^{-\lambda t})^{N-k}$ of the exp-clock waiting time, integrated over $(0,\infty)$. Equivalently $\binom{N}{k}\cdot(\text{integral}) = \frac{1}{\lambda(N-k)}$. Proved by the substitution $u=1-e^{-\lambda t}$ (mapping $(0,\infty)\to(0,1)$ with Jacobian $\lambda e^{-\lambda t}$) reducing to the Beta integral $\frac{1}{\lambda}\int_0^1 u^k(1-u)^{N-k-1}\,du = \frac{1}{\lambda}\cdot\frac{k!(N-k-1)!}{N!}$.
-- source:
--   Siegel, "Median Bounds and their Application", J. Algorithms 38:184-236, 2001, §2.1.1 (waiting-time / exponential-clock model); the survival-function term integrals giving $E[T]=\frac{1}{\lambda}\sum_{k=0}^{m}\frac{1}{N-k}$.

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

theorem waiting_survival_per_term_integral (N k : ℕ) (lam : ℝ) (hlam : 0 < lam) (hk : k < N) :
    ∫ t in Ioi (0:ℝ), (1 - Real.exp (-(lam * t))) ^ k * (Real.exp (-(lam * t))) ^ (N - k)
      = (1 / lam) * ((Nat.factorial k * Nat.factorial (N - k - 1) : ℝ) / Nat.factorial N) := by sorry
