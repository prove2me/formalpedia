-- Prove2me | Theorems.Thm_FermatPosition_degenerate_second_block_le
-- name    : FermatPosition.degenerate_second_block_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:28:45.273381+00:00
-- url     : https://prove2.me/theorems/e8e0300c-1173-4481-872d-85063c2b9388
-- title:
--   The second block `[2^n, 2^{n+1})` of the degenerate sieve carries at most one hit.
-- statement:
--   The second block `[2^n, 2^{n+1})` of the degenerate sieve carries at most one hit.
--
--   ```lean
--   theorem FermatPosition.degenerate_second_block_le(n : ℕ) : posCount degHit (2 ^ n) (2 ^ n) ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/FermatPositionNonlocality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/FermatPositionNonlocality.lean#L114

-- Thm stub generated from NumberTheory/FermatPositionNonlocality.lean
import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
import Definitions.Def_NumberTheory_FermatPositionNonlocality
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

open FermatPosition

open Finset



instance : DecidablePred degHit := fun _ => by unfold degHit; infer_instance

theorem FermatPosition.degenerate_second_block_le(n : ℕ) : posCount degHit (2 ^ n) (2 ^ n) ≤ 1 := by sorry
