-- Prove2me | solution 1 for CFPeriodNull.cheap_gcds_m2_add_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:35:54.975681+00:00
-- url     : https://prove2.me/submissions/9b587c93-380b-4997-a649-93797a6aa286

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
theorem solution(m : ℤ) :
    Int.gcd m (m ^ 2 + 1) = 1 ∧
      ((Int.gcd (m - 1) (m ^ 2 + 1) : ℤ) ∣ 2) ∧
      ((Int.gcd (m + 1) (m ^ 2 + 1) : ℤ) ∣ 2) := by
  refine ⟨Int.isCoprime_iff_gcd_eq_one.mp ⟨-m, 1, by ring⟩, ?_, ?_⟩
  · have h1 : (Int.gcd (m - 1) (m ^ 2 + 1) : ℤ) ∣ m - 1 := Int.gcd_dvd_left _ _
    have h2 : (Int.gcd (m - 1) (m ^ 2 + 1) : ℤ) ∣ m ^ 2 + 1 := Int.gcd_dvd_right _ _
    have h3 : (2 : ℤ) = (m ^ 2 + 1) - (m - 1) * (m + 1) := by ring
    rw [h3]
    exact dvd_sub h2 (h1.mul_right _)
  · have h1 : (Int.gcd (m + 1) (m ^ 2 + 1) : ℤ) ∣ m + 1 := Int.gcd_dvd_left _ _
    have h2 : (Int.gcd (m + 1) (m ^ 2 + 1) : ℤ) ∣ m ^ 2 + 1 := Int.gcd_dvd_right _ _
    have h3 : (2 : ℤ) = (m ^ 2 + 1) - (m + 1) * (m - 1) := by ring
    rw [h3]
    exact dvd_sub h2 (h1.mul_right _)
