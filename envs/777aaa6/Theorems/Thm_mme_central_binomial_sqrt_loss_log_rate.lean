-- Prove2me | Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
-- name    : mme_central_binomial_sqrt_loss_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T23:44:01.003462+00:00
-- url     : https://prove2.me/theorems/d960bc8f-cfa5-4a23-84e3-8c90f5a32347
-- title:
--   Central-binomial logarithmic rate survives the explicit square-root hashing loss
-- statement:
--   Let $C$ be a fixed real constant and $\delta>0$. For all sufficiently large natural $n$, uniformly for every positive real $x$,
--
--   $$\binom{2n}{n}\exp(-2C\sqrt{n+1})\le4x
--   \quad\Longrightarrow\quad
--   2n(\log 2-\delta)\le\log x.$$
--
--   All logarithms are natural. This derives the rate from the finite central-binomial lower bound and its explicit loss, with no convergence assumption about $x$. The threshold is independent of $x$, so the theorem applies to $x=AH$ after selecting a finite induced family at each power.
-- source:
--   Finite-rate analytic consequence of the uniform shared-Z hashing counts in Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9(1990), journal pp.270–271, https://doi.org/10.1016/S0747-7171(08)80013-2. The proof uses the already Proved bound2^k≤(k+1)choose(k,k/2), Prove2Me43ac5032-598c-4912-a288-e1d0c507811c, at k=2n, and the proved logarithmic/square-root loss absorption. This is an explicit analytic adapter, not a separately numbered source theorem or a tensor-value bound.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Choose.Sum

open Filter Topology

set_option autoImplicit false

theorem mme_central_binomial_sqrt_loss_log_rate (C delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      ∀ x : ℝ, 0 < x →
        (Nat.choose (2 * n) n : ℝ) *
            Real.exp (-2 * C * Real.sqrt (((n + 1 : ℕ) : ℝ))) ≤ 4 * x →
          (2 * (n : ℝ)) * (Real.log 2 - delta) ≤ Real.log x := by sorry
