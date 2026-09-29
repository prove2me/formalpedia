-- Prove2me | solution 1 for CFPeriodNull.sqrt_one_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:37:22.399819+00:00
-- url     : https://prove2.me/submissions/3fe34df2-7844-4b59-a9c4-51aba57e5697

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
theorem solution(p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ) (x : ℤ)
    (hx : ((p : ℤ) ^ k) ∣ x ^ 2 - 1) :
    ((p : ℤ) ^ k) ∣ x - 1 ∨ ((p : ℤ) ^ k) ∣ x + 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hfac : ((p : ℤ) ^ k) ∣ (x - 1) * (x + 1) := by
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, by linear_combination hc⟩
  by_cases hdvd : (p : ℤ) ∣ x - 1
  · -- then `p ∤ x + 1`, since otherwise `p ∣ 2`
    by_cases hdvd2 : (p : ℤ) ∣ x + 1
    · exfalso
      have h2 : (p : ℤ) ∣ 2 := by
        have := dvd_sub hdvd2 hdvd
        simpa using this
      have hple : (p : ℕ) ∣ 2 := by exact_mod_cast h2
      rcases (Nat.dvd_prime Nat.prime_two).mp hple with h | h
      · exact hp.one_lt.ne' h
      · exact hodd h
    · left
      have hcop : IsCoprime ((p : ℤ) ^ k) (x + 1) :=
        (hpZ.coprime_iff_not_dvd.mpr hdvd2).pow_left
      exact hcop.dvd_of_dvd_mul_right hfac
  · right
    have hcop : IsCoprime ((p : ℤ) ^ k) (x - 1) :=
      (hpZ.coprime_iff_not_dvd.mpr hdvd).pow_left
    exact hcop.dvd_of_dvd_mul_left hfac
