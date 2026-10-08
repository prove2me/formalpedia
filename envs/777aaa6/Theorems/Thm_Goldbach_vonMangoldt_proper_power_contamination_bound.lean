-- Prove2me | Theorems.Thm_Goldbach_vonMangoldt_proper_power_contamination_bound
-- name    : Goldbach.vonMangoldt_proper_power_contamination_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:06:17.69621+00:00
-- url     : https://prove2.me/theorems/1ed98835-8063-48dc-a7e6-979b6cb85df3
-- title:
--   Proper prime-power contamination in the binary von Mangoldt convolution
-- statement:
--   Let $\Lambda$ be the von Mangoldt function on natural numbers: it equals $\log p$ at a positive power of a prime $p$, and is zero otherwise. For every natural number $N$, put $M=\lfloor\sqrt N\rfloor$ and $K=\lfloor\log_2N\rfloor$, using the natural logarithm-to-base-two convention $K=0$ at $N=0$.
--
--   The part of the ordered binary convolution contributed by pairs that are not both prime satisfies
--
--   $$
--   \sum_{m=0}^{N}\mathbf1_{\neg(m\text{ prime}\ \land\ N-m\text{ prime})}\Lambda(m)\Lambda(N-m)
--   \le 2MK(\log N)^2.
--   $$
--
--   This is an unconditional elementary finite-support estimate. It removes the proper-prime-power contribution when transferring analytic lower bounds for a von Mangoldt convolution to actual prime-pair counts. It supplies no lower bound for that convolution and does not prove strong Goldbach.
--
--   Formalization note: the square root and base-two logarithm are `Nat.sqrt` and `Nat.log 2`; the real logarithm at zero follows Mathlib's convention `Real.log 0 = 0`. The endpoint sum includes both $m=0$ and $m=N$.
-- source:
--   Elementary finite-support estimate developed for the Goldbach mission, https://prove2.me/missions/The_Goldbach_Conjecture. Uses Mathlib ArithmeticFunction.vonMangoldt and Nat.sqrt/Nat.log APIs; no claim of a new prime-distribution estimate or literature novelty.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.vonMangoldt_proper_power_contamination_bound (N : ℕ) :
    (∑ m ∈ Finset.range (N+1),
      if Nat.Prime m ∧ Nat.Prime (N-m) then (0:ℝ) else
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m)) ≤
    2 * (Nat.sqrt N * Nat.log 2 N : ℕ) * (Real.log N)^2 := by sorry
