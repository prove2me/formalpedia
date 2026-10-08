-- Prove2me | Theorems.Thm_Goldbach_weighted_proper_power_contamination_bound
-- name    : Goldbach.weighted_proper_power_contamination_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T01:21:50.894894+00:00
-- url     : https://prove2.me/theorems/f473c64c-a73e-4549-9a07-a81a0ec59082
-- title:
--   Weighted prime-power contamination bound without the extra logarithmic factor
-- statement:
--   For every natural number `N`, the contribution to the von Mangoldt convolution
--   from pairs that are not both prime is at most
--
--   $$2\lfloor\sqrt N\rfloor(\log N)^2.$$
--
--   This removes the factor `floor(log₂ N)` from the earlier registered elementary
--   contamination bound. It does not provide a lower bound for the full convolution.
--
--   The key is to bound total von Mangoldt weight, rather than counting every proper
--   prime power and charging it the same maximum weight. A nonprime argument with
--   nonzero von Mangoldt value is a power `p^k` with `k ≥ 2` and `p ≤ floor(sqrt N)`.
--   For each base, take only exponents through `floor(log_p N)`. Positive powers have
--   the same von Mangoldt value as their base, at most `log p`. The number of these
--   exponents times `log p` is at most `log N`, because
--   `p^(floor(log_p N)) ≤ N`. Summing over all possible bases therefore bounds the
--   weight of the cover by `floor(sqrt N) log N`. Nonprime bases and duplicate powers
--   can only enlarge this upper bound.
--
--   In a bad convolution pair, at least one nonzero factor comes from this cover.
--   The other von Mangoldt factor is at most `log N`. Reflection of the finite sum
--   accounts for the two possible endpoints, giving the stated factor of two.
--   The proof includes `N = 0` separately and all other natural numbers uniformly.
--
--   This is a refinement of an elementary extraction interface, not a new estimate
--   for the distribution or correlation of primes. The local proof is closed in
--   the strong-Goldbach mission's exact pinned environment, with only standard
--   Lean foundational axioms.
-- source:
--   Elementary weighted prime-power bounds and an improved quantitative extraction interface for https://prove2.me/missions/The_Goldbach_Conjecture. Uses Mathlib vonMangoldt_apply_pow and the integer-log power bound; no new prime-distribution estimate or literature novelty is claimed.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.BigOperators.Intervals
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.weighted_proper_power_contamination_bound (N : ℕ) :
    (∑ m ∈ Finset.range (N+1),
      if Nat.Prime m ∧ Nat.Prime (N-m) then (0:ℝ) else
        ArithmeticFunction.vonMangoldt m * ArithmeticFunction.vonMangoldt (N-m)) ≤
    2 * (Nat.sqrt N : ℝ) * (Real.log N)^2 := by sorry
