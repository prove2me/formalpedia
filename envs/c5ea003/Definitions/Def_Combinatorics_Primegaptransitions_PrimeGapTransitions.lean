-- Prove2me | Definitions.Def_Combinatorics_Primegaptransitions_PrimeGapTransitions
-- name    : Combinatorics_Primegaptransitions_PrimeGapTransitions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:45:00.331002+00:00
-- url     : https://prove2.me/theorems/b2edf7ab-faa4-4c86-9f40-5f978799a48a
-- title:
--   Aether Catalog definitions — Combinatorics_Primegaptransitions_PrimeGapTransitions
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.Primegaptransitions.PrimeGapTransitions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/Primegaptransitions/PrimeGapTransitions.lean by skeleton subtraction
import Mathlib

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

namespace PrimeGap

open Nat

/-! ## A block of consecutive composites -/


/-! ## Consecutive primes -/

/-- The least prime `≥ N`. -/
noncomputable def nextPrime (N : ℕ) : ℕ := sInf {p | N ≤ p ∧ p.Prime}






/-- The greatest prime `< N`, for `N ≥ 3`. -/
noncomputable def prevPrime (N : ℕ) : ℕ :=
  sSup {p | p < N ∧ p.Prime}




/-! ## Unbounded gaps -/


end PrimeGap


