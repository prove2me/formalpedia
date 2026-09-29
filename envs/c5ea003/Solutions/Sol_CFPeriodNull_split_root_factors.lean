-- Prove2me | solution 1 for CFPeriodNull.split_root_factors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:37:21.65751+00:00
-- url     : https://prove2.me/submissions/d8058b57-a900-412b-aa08-bf8e454f84fb

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
theorem solution(n : ℕ) (hn : 1 < n) (x : ℤ) (hx : (n : ℤ) ∣ x ^ 2 - 1)
    (h1 : ¬ (n : ℤ) ∣ x - 1) (h2 : ¬ (n : ℤ) ∣ x + 1) :
    1 < Int.gcd (x - 1) (n : ℤ) ∧ Int.gcd (x - 1) (n : ℤ) < n ∧
      Int.gcd (x - 1) (n : ℤ) ∣ n := by
  set g : ℕ := Int.gcd (x - 1) (n : ℤ) with hg
  have hgdvd : (g : ℤ) ∣ (n : ℤ) := Int.gcd_dvd_right _ _
  have hgdvdn : g ∣ n := Int.ofNat_dvd.mp hgdvd
  have hgx : (g : ℤ) ∣ x - 1 := Int.gcd_dvd_left _ _
  have hgne1 : g ≠ 1 := by
    intro h
    have hcop : IsCoprime (x - 1) (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr h
    have : (n : ℤ) ∣ (x - 1) * (x + 1) := by
      obtain ⟨c, hc⟩ := hx
      exact ⟨c, by linear_combination hc⟩
    exact h2 (hcop.symm.dvd_of_dvd_mul_left this)
  have hgnen : g ≠ n := fun h => h1 (by rw [← h] at hgdvd ⊢; exact hgx)
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgdvdn (by omega)
  refine ⟨by omega, ?_, hgdvdn⟩
  exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) hgdvdn) hgnen
