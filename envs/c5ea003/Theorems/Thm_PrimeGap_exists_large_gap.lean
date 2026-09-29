-- Prove2me | Theorems.Thm_PrimeGap_exists_large_gap
-- name    : PrimeGap.exists_large_gap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:25:58.566407+00:00
-- url     : https://prove2.me/theorems/15963245-32c2-4434-b157-41f4f21025a1
-- title:
--   Prime gaps are unbounded.
-- statement:
--   **Prime gaps are unbounded.**  For every `n` there are two primes `p < q` with
--   `n ≤ q - p` and no prime strictly in between: a "prime gap transition" of size at
--   least `n`.
--
--   ```lean
--   theorem PrimeGap.exists_large_gap(n : ℕ) :
--       ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n ≤ q - p ∧ ∀ r, p < r → r < q → ¬ r.Prime := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Primegaptransitions/PrimeGapTransitions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Primegaptransitions/PrimeGapTransitions.lean#L84

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


/-! ## Consecutive primes -/











/-! ## Unbounded gaps -/

theorem PrimeGap.exists_large_gap(n : ℕ) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n ≤ q - p ∧ ∀ r, p < r → r < q → ¬ r.Prime := by sorry
