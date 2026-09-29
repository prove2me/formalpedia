-- Prove2me | Theorems.Thm_Hashimoto_revWalk_ne
-- name    : Hashimoto.revWalk_ne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:36:06.010476+00:00
-- url     : https://prove2.me/theorems/32e98049-4a0a-4a23-8c0c-b8da36b3896d
-- title:
--   Reversal has no fixed point: the root of the reversed walk is the reversal of the
-- statement:
--   Reversal has no fixed point: the root of the reversed walk is the reversal of the
--   root, and no dart equals its own reversal.
--
--   ```lean
--   theorem Hashimoto.revWalk_ne{n : ℕ} {l : List G.Dart} (hl : l ∈ closedNBWalks G n) :
--       revWalk l ≠ l := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/ReversalParity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/ReversalParity.lean#L80

-- Thm stub generated from Algebra/NonBacktracking/ReversalParity.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_ReversalParity

/-!
# Reversal of non-backtracking walks and parity of the trace

Reversing a walk and flipping each of its darts is an involution on the set of rooted
closed non-backtracking walks. It has **no fixed point**: the root of the reversed walk
is the reversal of the root, and a dart is never equal to its own reversal. Consequently

`trace (B ^ n)` is even for every `n`.

For `n = 0` this recovers the classical handshake statement (the number of darts is even);
for `n ≥ 1` it says that closed non-backtracking walks come in genuinely distinct
clockwise/anticlockwise pairs.

## Main results

* `Hashimoto.even_card_of_involution` — a finset carrying a fixed-point-free involution
  has even cardinality (proved by summing the constant `1` over `ZMod 2`).
* `Hashimoto.revWalk_mem` — reversal preserves rooted closed non-backtracking walks.
* `Hashimoto.even_trace_hashimoto_pow` — `Even (trace (B ^ n))`.
-/

open Finset SimpleGraph List

open Hashimoto

/-! ## A parity tool -/


/-! ## Reversal of dart walks -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Hashimoto.revWalk_ne{n : ℕ} {l : List G.Dart} (hl : l ∈ closedNBWalks G n) :
    revWalk l ≠ l := by sorry
