-- Prove2me | Definitions.Def_NumberTheory_FermatPositionNonlocality
-- name    : NumberTheory_FermatPositionNonlocality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:41.618628+00:00
-- url     : https://prove2.me/theorems/68f9474a-77d8-42ac-b12d-402b2d684443
-- title:
--   Aether Catalog definitions — NumberTheory_FermatPositionNonlocality
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.FermatPositionNonlocality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/FermatPositionNonlocality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
/-
# Non-locality of the smooth locus

Fourth companion to `Catalog/NumberTheory/FermatPositionGeometry.lean`.

The previous files established a dichotomy for the sieve polynomial
`v(j) = (b + j)^2 - N`:

* every *local* (finite-modulus) position property — divisibility by a fixed prime, by a
  fixed prime power, or a nontrivial gcd with the base value — is exactly periodic and
  hence has discrepancy at most its modulus in any window
  (`FermatPosition.periodic_block_balance`);
* while the *magnitude* of `v(j)` grows linearly in `j` (`FermatPosition.sieveVal_sandwich`).

This file closes the dichotomy by showing that the smooth locus itself is **not** local:
there is no modulus `T` and no predicate on `ZMod T` describing the positions carrying a
smooth value.  The witness is the degenerate sieve `b = 1`, `N = 0`, whose values are the
squares `(j+1)^2`, `3`-smooth exactly at the powers of two: a block of length `2^n`
starting at `0` carries at least `n + 1` hits while the next block of the same length
carries at most one.

Consequences for the positional-structure question: a small-`j` excess of `E` hits over
an equally long block can only be produced by a local carrier of modulus `T ≥ E`
(`periodic_block_balance`), and cannot be produced by *any* local carrier when the excess
grows with the window — the non-local, magnitude-driven component of smoothness is
unavoidable.

Main results.

* `smooth3_iff` : `n` is `3`-smooth iff `n` is a power of two.
* `degenerate_hit_iff` : the hit positions of the degenerate sieve are `2^k - 1`.
* `smooth_locus_block_imbalance` : block `[0, 2^n)` has at least `n+1` hits, block
  `[2^n, 2^{n+1})` has at most one.
* `smooth_locus_not_local` : for every `T` there is a pair of equal-length blocks whose
  hit counts differ by more than `T`.
* `no_local_description_of_smooth_locus` : consequently no `ZMod T`-predicate describes
  the smooth locus, for any modulus `T`.
-/

namespace FermatPosition

open Finset


/-- The hit predicate of the degenerate sieve `b = 1`, `N = 0` at smoothness bound `3`. -/
def degHit (j : ℤ) : Prop := (sieveVal 1 0 j).natAbs ∈ Nat.smoothNumbers 3

instance : DecidablePred degHit := fun _ => by unfold degHit; infer_instance







end FermatPosition


