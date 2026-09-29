-- Prove2me | Theorems.Thm_PrimeGap_exists_consecutive_composites
-- name    : PrimeGap.exists_consecutive_composites
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:25:51.82641+00:00
-- url     : https://prove2.me/theorems/fa0c7654-1e5b-4f33-b1b6-25036dfca3bb
-- title:
--   For every `n` there are `n` consecutive composite numbers, starting at
-- statement:
--   For every `n` there are `n` consecutive composite numbers, starting at
--   `(n+1)! + 2`.  Indeed `(k+2) ∣ (n+1)!` for `k < n`, so `(k+2) ∣ (n+1)! + 2 + k`.
--
--   ```lean
--   theorem PrimeGap.exists_consecutive_composites(n : ℕ) :
--       ∃ m, 3 ≤ m ∧ ∀ k < n, ¬ Nat.Prime (m + k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Primegaptransitions/PrimeGapTransitions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Primegaptransitions/PrimeGapTransitions.lean#L27

-- Thm stub generated from Combinatorics/Primegaptransitions/PrimeGapTransitions.lean
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

theorem PrimeGap.exists_consecutive_composites(n : ℕ) :
    ∃ m, 3 ≤ m ∧ ∀ k < n, ¬ Nat.Prime (m + k) := by sorry
