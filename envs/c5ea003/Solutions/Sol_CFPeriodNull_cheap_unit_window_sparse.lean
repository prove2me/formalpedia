-- Prove2me | solution 1 for CFPeriodNull.cheap_unit_window_sparse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:35:55.865382+00:00
-- url     : https://prove2.me/submissions/77e06cf1-8a1f-4a9a-8c1b-7172a750042e

-- Sol generated from Shared/CFPeriodNull.lean
import Mathlib
import Definitions.Def_Shared_CFPeriodNull
/-
# CFPERIOD-NULL: the continued-fraction period of `√N` as a symmetric channel

Formal core for Experiment 398.  We build the PQa (continued fraction of `√N`)
state machine over `ℤ`, prove its complete set of integral invariants, and
deduce the Pell/fundamental-unit output.
-/

open CFPeriodNull

/-! ## 1. The PQa state machine -/








/-! ## 2. The Pell / fundamental-unit output of the machine -/



/-! ## 3. The concrete continued fraction of `√N` -/






/-! ## 4. The one factor-adjacent exit: a split square root of `1 mod N` -/



/-! ## 5. The negative-Pell dichotomy: a pure congruence bit -/





/-! ## 6. The cheap-period window carries no leverage -/






/-! ## 7. The cheap window is a density-zero family -/


/-! ## 8. Dirichlet no-pinning: the congruence bit never pins a factor -/



/-! ## 9. De-confounding: every partial quotient is pinned by `⌊√N⌋`

The raw experiment found `corr(max partial quotient, s) ≈ +0.99` in every
bucket; the reason is that the maximal partial quotient of `√N` is exactly
`2⌊√N⌋`, a pure `N`-size coordinate.  Here we prove both halves:
`a_k ≤ 2⌊√N⌋` for every `k ≥ 1`, with equality at the end of a period. -/












/-! ## 10. Verified instances (Lab Notes)

Machine-checked instances of the whole pipeline.  The computed period table for
`2 ≤ N ≤ 40` (non-squares) reproduces OEIS A003285:

```
N : 2  3  5  6  7  8 10 11 12 13 14 15 17 18 19 20 21 22 23 24 26 27 28 29 31
l : 1  2  1  2  4  2  1  2  2  5  4  2  1  2  6  2  6  6  4  2  1  2  4  5  8
```

with period-end unit norms `-1` exactly on the odd periods
(`N = 2, 5, 10, 13, 17, 26, 29, 37`), confirming the negative-Pell dichotomy.
-/









/-! ## 11. The exit is *exactly* the split-root event: prime powers are immune

Cycle-2 result.  The only factor-adjacent exit of the channel (Section 4) fires
only when `N` has at least two distinct prime factors: modulo an odd prime power
every square root of `1` is `± 1`, so the continued fraction of `√(p^k)` — no
matter how long its period — can never split `N`. -/





/-! ## 12. Cost side: denominators grow like Fibonacci, `d` stays `≤ 2⌊√N⌋`

Cycle-3 results.  The period-end witness is *exponentially large in the period*
(`q_l ≥ fib l`), while all the intermediate data stay inside the box
`0 ≤ m ≤ ⌊√N⌋`, `0 < d ≤ 2⌊√N⌋`.  So the channel's only unbounded coordinate is
the *number of steps*, which is what makes it a `O(√N)`-cost object rather than
a `poly(log N)` witness. -/





open CFPeriodNull in
theorem solution(y X : ℕ) (hy : 1 ≤ y) :
    ((Finset.range (X + 1)).filter
        (fun N => (Nat.sqrt (N * y ^ 2 + 1)) ^ 2 = N * y ^ 2 + 1)).card
      ≤ Nat.sqrt (X * y ^ 2 + 1) + 1 := by
  have hmap : Set.MapsTo (fun N => Nat.sqrt (N * y ^ 2 + 1))
      ↑((Finset.range (X + 1)).filter
        (fun N => (Nat.sqrt (N * y ^ 2 + 1)) ^ 2 = N * y ^ 2 + 1))
      ↑(Finset.range (Nat.sqrt (X * y ^ 2 + 1) + 1)) := by
    intro N hN
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hN
    have hle : N * y ^ 2 + 1 ≤ X * y ^ 2 + 1 :=
      Nat.succ_le_succ (Nat.mul_le_mul_right _ (by omega))
    simpa using Nat.lt_succ_of_le (Nat.sqrt_le_sqrt hle)
  have hinj : Set.InjOn (fun N => Nat.sqrt (N * y ^ 2 + 1))
      ↑((Finset.range (X + 1)).filter
        (fun N => (Nat.sqrt (N * y ^ 2 + 1)) ^ 2 = N * y ^ 2 + 1)) := by
    intro N₁ h₁ N₂ h₂ heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at h₁ h₂
    have hy2 : 0 < y ^ 2 := by positivity
    have heq' : Nat.sqrt (N₁ * y ^ 2 + 1) = Nat.sqrt (N₂ * y ^ 2 + 1) := heq
    have e1 := h₁.2
    rw [heq', h₂.2] at e1
    exact Nat.eq_of_mul_eq_mul_right hy2 (by omega)
  simpa using Finset.card_le_card_of_injOn _ hmap hinj
