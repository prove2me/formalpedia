-- Prove2me | solution 1 for CFPeriodNull.cf_q_ge_fib
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:35:54.0649+00:00
-- url     : https://prove2.me/submissions/20af1a54-801e-4a4f-bb2e-ee5f2e1b61b1

-- Sol generated from Shared/CFPeriodNull.lean
import Mathlib
import Definitions.Def_Shared_CFPeriodNull
import Theorems.Thm_CFPeriodNull_partial_quotient_bounds
import Theorems.Thm_CFPeriodNull_red_first
import Theorems.Thm_CFPeriodNull_red_step
import Theorems.Thm_CFPeriodNull_step_inv
/-
# CFPERIOD-NULL: the continued-fraction period of `√N` as a symmetric channel

Formal core for Experiment 398.  We build the PQa (continued fraction of `√N`)
state machine over `ℤ`, prove its complete set of integral invariants, and
deduce the Pell/fundamental-unit output.
-/

open CFPeriodNull

/-! ## 1. The PQa state machine -/





theorem inv_init (N : ℤ) : Inv N CFState.init := by
  constructor <;> simp [CFState.init]



/-! ## 2. The Pell / fundamental-unit output of the machine -/



/-! ## 3. The concrete continued fraction of `√N` -/



/-- All PQa invariants hold along the continued fraction of `√N`, for every
non-square `N`. -/
theorem cfRun_inv (N : ℕ) (hN : ∀ z : ℤ, z ^ 2 ≠ (N : ℤ)) (k : ℕ) :
    Inv (N : ℤ) (cfRun N k) := by
  induction k with
  | zero => exact inv_init _
  | succ k ih => exact step_inv _ hN _ _ ih



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







/-- The continued fraction of a non-square `N ≥ 1` is reduced from step `1` on. -/
theorem red_run (N : ℕ) (hN : ∀ z : ℤ, z ^ 2 ≠ (N : ℤ)) (hN1 : 1 ≤ N) (k : ℕ) :
    Red N (cfRun N (k + 1)) := by
  induction k with
  | zero => exact red_first N hN hN1
  | succ k ih => exact red_step N hN _ (cfRun_inv N hN (k + 1)) ih





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
theorem solution(N : ℕ) (hN : ∀ z : ℤ, z ^ 2 ≠ (N : ℤ)) (hN1 : 1 ≤ N) :
    ∀ k : ℕ, ((Nat.fib k : ℤ) ≤ (cfRun N (k + 1)).qp ∧
      (Nat.fib (k + 1) : ℤ) ≤ (cfRun N (k + 1)).q) := by
  intro k
  induction k with
  | zero =>
      have hstate : cfRun N 1 = ⟨a0 N, (N : ℤ) - a0 N ^ 2, 1, a0 N, 0, 1⟩ := by
        simp [cfRun, cfNext, step, CFState.init, a0]
      rw [hstate]
      exact ⟨by simp, by simp⟩
  | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hred := red_run N hN hN1 k
      have ha1 : 1 ≤ (a0 N + (cfRun N (k + 1)).m) / (cfRun N (k + 1)).d :=
        (partial_quotient_bounds N _ hred).1
      have hqp : (cfRun N (k + 2)).qp = (cfRun N (k + 1)).q := rfl
      have hq : (cfRun N (k + 2)).q =
          ((a0 N + (cfRun N (k + 1)).m) / (cfRun N (k + 1)).d) * (cfRun N (k + 1)).q
            + (cfRun N (k + 1)).qp := rfl
      have hfib0 : (0 : ℤ) ≤ (Nat.fib k : ℤ) := by positivity
      have hfib1 : (0 : ℤ) ≤ (Nat.fib (k + 1) : ℤ) := by positivity
      refine ⟨by rw [hqp]; exact ih2, ?_⟩
      rw [hq, Nat.fib_add_two]
      push_cast
      nlinarith
