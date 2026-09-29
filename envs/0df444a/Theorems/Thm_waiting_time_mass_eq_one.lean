-- Prove2me | Theorems.Thm_waiting_time_mass_eq_one
-- name    : waiting_time_mass_eq_one
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:21:10.107791+00:00
-- url     : https://prove2.me/theorems/c28346f7-000a-4d7c-a455-7246ce947a9f
-- title:
--   The waiting-time density has total mass one
-- statement:
--   **Waiting-time density has total mass 1.** For integers $0 \le m < N$ and rate $\lambda > 0$, the Siegel waiting-time density $f(t) = N\binom{N-1}{m}(1-e^{-\lambda t})^m (e^{-\lambda t})^{N-m}\lambda$ integrates to $1$ over $(0,\infty)$: $\int_0^\infty f(t)\,dt = 1$. This is the normalization (probability-measure) property of the waiting time $T = \min\{s : X_N(s) \ge m+1\}$ for $N$ independent rate-$\lambda$ exponential clocks, established by the fundamental theorem of calculus from the CDF $F(t)=\sum_{k=m+1}^{N}\binom{N}{k}(1-e^{-\lambda t})^k (e^{-\lambda t})^{N-k}$ (which satisfies $F(0)=0$ and $F(t)\to 1$ as $t\to\infty$).
-- source:
--   Siegel, "Median Bounds and their Application", J. Algorithms 38:184-236, 2001, §2.1.1 (Theorem 2.2 setup); the density $f_T$ on p.6. Mass-1 is the statement that $F$ is a CDF.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Filter.AtTopBot.Field

set_option autoImplicit false
open scoped BigOperators
open Finset MeasureTheory Set Filter Topology

theorem waiting_time_mass_eq_one (N m : ℕ) (lam : ℝ) (h : m < N) (hlam : 0 < lam) :
    ∫ s in Set.Ioi (0:ℝ),
      ((N : ℝ) * (Nat.choose (N-1) m : ℝ) * (1 - Real.exp (-(lam * s))) ^ m
        * (Real.exp (-(lam * s))) ^ (N - m) * lam) = 1 := by sorry
