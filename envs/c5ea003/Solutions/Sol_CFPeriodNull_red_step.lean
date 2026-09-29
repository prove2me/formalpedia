-- Prove2me | solution 1 for CFPeriodNull.red_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:33:15.898988+00:00
-- url     : https://prove2.me/submissions/f52cda4c-d9cc-4c1b-87f5-635c9017ffb9

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


theorem a0_sq_lt (N : ℕ) (hN : ∀ z : ℤ, z ^ 2 ≠ (N : ℤ)) : a0 N ^ 2 < (N : ℤ) := by
  have h : Nat.sqrt N ^ 2 ≤ N := Nat.sqrt_le' N
  refine lt_of_le_of_ne ?_ (hN _)
  simp only [a0]
  exact_mod_cast h

theorem lt_a0_succ_sq (N : ℕ) : (N : ℤ) < (a0 N + 1) ^ 2 := by
  have h : N < (Nat.sqrt N).succ ^ 2 := Nat.lt_succ_sqrt' N
  simp only [a0]
  exact_mod_cast h









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
theorem solution(N : ℕ) (hN : ∀ z : ℤ, z ^ 2 ≠ (N : ℤ)) (s : CFState)
    (hinv : Inv (N : ℤ) s) (hs : Red N s) : Red N (cfNext N s) := by
  obtain ⟨hd, hm0, hmA, hdA, hAd⟩ := hs
  have hlt := a0_sq_lt N hN
  have hgt := lt_a0_succ_sq N
  set A : ℤ := a0 N with hA
  set a : ℤ := (A + s.m) / s.d with ha
  set r : ℤ := (A + s.m) % s.d with hr
  have hsum : s.d * a + r = A + s.m := Int.mul_ediv_add_emod _ _
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hd)
  have hrd : r < s.d := Int.emod_lt_of_pos _ hd
  -- the new `m` is exactly `A - r`
  have hmnew : s.d * a - s.m = A - r := by linarith
  have ha1 : 1 ≤ a := by
    by_contra hcon
    push_neg at hcon
    have : s.d * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hd.le (by omega)
    linarith
  -- `m' ≥ 0`, i.e. `r ≤ A`
  have hrA : r ≤ A := by
    rcases le_or_gt s.d A with hcase | hcase
    · linarith
    · have haeq : a = 1 := by nlinarith
      rw [haeq] at hsum
      linarith
  have hm'0 : 0 ≤ A - r := by linarith
  have hm'A : A - r ≤ A := by linarith
  -- the new `d`
  have hdvd : s.d ∣ (N : ℤ) - (s.d * a - s.m) ^ 2 := by
    obtain ⟨c, hc⟩ := hinv.ddvd
    exact ⟨c + (2 * a * s.m - a ^ 2 * s.d), by linear_combination hc⟩
  have hdd' : s.d * (((N : ℤ) - (s.d * a - s.m) ^ 2) / s.d)
      = (N : ℤ) - (s.d * a - s.m) ^ 2 := Int.mul_ediv_cancel' hdvd
  set d' : ℤ := ((N : ℤ) - (s.d * a - s.m) ^ 2) / s.d with hd'def
  rw [hmnew] at hdd'
  -- positivity of the new `d`
  have hNm : (A - r) ^ 2 < (N : ℤ) := by nlinarith
  have hd'pos : 0 < d' := by nlinarith
  -- `d ≤ m + m'`, from `d * a = m + m'` and `a ≥ 1`
  have hdsmall : s.d ≤ s.m + (A - r) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show 0 < d'
    exact hd'pos
  · show 0 ≤ s.d * a - s.m
    rw [hmnew]; exact hm'0
  · show s.d * a - s.m ≤ A
    rw [hmnew]; exact hm'A
  · show d' ≤ A + (s.d * a - s.m)
    rw [hmnew]
    by_contra hcon
    push_neg at hcon
    nlinarith
  · show A < d' + (s.d * a - s.m)
    rw [hmnew]
    by_contra hcon
    push_neg at hcon
    nlinarith
