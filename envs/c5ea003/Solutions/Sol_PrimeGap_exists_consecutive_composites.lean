-- Prove2me | solution 1 for PrimeGap.exists_consecutive_composites
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:13:46.421088+00:00
-- url     : https://prove2.me/submissions/6539f8bb-2d59-49cb-9358-fef7de818955

-- Sol generated from Combinatorics/Primegaptransitions/PrimeGapTransitions.lean
import Mathlib
import Definitions.Def_Combinatorics_Primegaptransitions_PrimeGapTransitions

/-!
# Prime gap transitions

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/PrimeGapTransitions.lean`.  It is reconstructed here as a
self-contained development of *transitions* between consecutive primes, i.e. the
gaps `q - p` for `p < q` consecutive primes.

Main results:

* `PrimeGap.exists_consecutive_composites` — for every `n` there is a block of `n`
  consecutive composite numbers (the factorial construction);
* `PrimeGap.nextPrime` and `PrimeGap.prevPrime` — the successor and predecessor
  primes of a given bound, together with the fact that nothing prime lies strictly
  in between (`PrimeGap.no_prime_between`);
* `PrimeGap.exists_large_gap` — **prime gaps are unbounded**: for every `n` there
  are consecutive primes `p < q` with `n ≤ q - p`.
-/

open PrimeGap

open Nat

/-! ## A block of consecutive composites -/


/-! ## Consecutive primes -/











/-! ## Unbounded gaps -/



open PrimeGap in
theorem solution(n : ℕ) :
    ∃ m, 3 ≤ m ∧ ∀ k < n, ¬ Nat.Prime (m + k) := by
  have hfac : 1 ≤ (n + 1)! := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine ⟨(n + 1)! + 2, by omega, ?_⟩
  intro k hk hp
  have hdvd1 : (k + 2) ∣ (n + 1)! := Nat.dvd_factorial (by omega) (by omega)
  have hdvd : (k + 2) ∣ ((n + 1)! + 2 + k) := by
    have : (n + 1)! + 2 + k = (n + 1)! + (k + 2) := by omega
    rw [this]
    exact Nat.dvd_add hdvd1 dvd_rfl
  have hne1 : k + 2 ≠ 1 := by omega
  have hne : k + 2 ≠ (n + 1)! + 2 + k := by omega
  exact hne ((Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd).resolve_left hne1)
