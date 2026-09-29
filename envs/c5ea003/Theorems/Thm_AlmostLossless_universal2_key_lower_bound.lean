-- Prove2me | Theorems.Thm_AlmostLossless_universal2_key_lower_bound
-- name    : AlmostLossless.universal2_key_lower_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:09:41.065003+00:00
-- url     : https://prove2.me/theorems/c9c3ef4b-e2e4-447a-9f2e-aef280ab3712
-- title:
--   Key-space lower bound.
-- statement:
--   **Key-space lower bound.**  A 2-universal family on a source of `n` symbols
--   with `M ≥ 2` codewords needs at least `log_M n` keys; equivalently the encoder
--   must be able to name `log₂ n / log₂ M` distinct hash functions.  Randomness
--   cannot be removed from Monte-Carlo compression, only compressed.
--
--   ```lean
--   theorem AlmostLossless.universal2_key_lower_bound{H : Fin K → α → Fin M} (hU : Universal2 H)
--       (hK : 0 < K) (hM : 2 ≤ M) : Nat.log M (Fintype.card α) ≤ K := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessKeyBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessKeyBound.lean#L69

-- Thm stub generated from Bridges/AlmostLosslessKeyBound.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessLinearHash
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression XI: How Much Randomness Does the Encoder Need?

## Bridge: pigeonhole (combinatorics) ↔ universal hashing (algebra)
##         ↔ derandomization (complexity)

Every achievability theorem of this development starts from a 2-universal family
`H : Fin K → α → Fin M` and *derandomizes* it (`exists_good_key`): the encoder
only has to store one key, i.e. `log₂ K` bits of advice.  Conjecture 5 of the
previous cycle asked how small `K` can be.  Here we prove a hard limit, and it
is the pigeonhole principle again — now applied to the **key space** rather than
to the code space:

* `universal2_card_le_pow` — a 2-universal family with `M ≥ 2` and at least one
  key, on a domain of size `n`, satisfies `n ≤ M^K`;
* `universal2_key_lower_bound` — equivalently `K ≥ log_M n`: the number of keys
  must grow at least logarithmically in the source size, so no constant-size
  family of hash functions can be universal on an unbounded source;
* `linHash_key_bound_sharp_order` — the explicit field family of
  `AlmostLosslessLinearHash` has `K = p` keys on a domain of size `p²`, meeting
  the bound `n ≤ M^K` with room to spare while using only `log₂ p` bits of
  advice: **half** the bits of the message it compresses.

The moral for Monte-Carlo compression: randomness cannot be eliminated, but
`log₂ K` bits of it always suffice, and the field construction already achieves
`log₂ K = ½ log₂ n`.

## Impact: key_space_lower_bound, derandomization_limits
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}


omit [DecidableEq α] in

theorem AlmostLossless.universal2_key_lower_bound{H : Fin K → α → Fin M} (hU : Universal2 H)
    (hK : 0 < K) (hM : 2 ≤ M) : Nat.log M (Fintype.card α) ≤ K := by sorry
