-- Prove2me | Theorems.Thm_AlmostLossless_card_silentSlice_mul_le
-- name    : AlmostLossless.card_silentSlice_mul_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:04:17.89989+00:00
-- url     : https://prove2.me/theorems/4ee52903-8bcc-4060-b0e6-783a9d24f8a9
-- title:
--   Fibrewise bound.
-- statement:
--   **Fibrewise bound.**  Once the hash codebook `H` is fixed, the candidate the
--   hash decoder proposes is determined; a silent corruption then requires the
--   independent checksum to collide on that single pair, an event of probability
--   `1/K`.
--
--   ```lean
--   theorem AlmostLossless.card_silentSlice_mul_le(L : List α) (x : α) (H : α → Fin M) :
--       K * (silentSlice L x H K).card ≤ K ^ Fintype.card α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessChecksum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessChecksum.lean#L90

-- Thm stub generated from Geometry/AlmostLosslessChecksum.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessChecksum
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# Closing the silent-corruption loophole: a random checksum layer

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

`Geometry.AlmostLosslessDecoder` proves that the scanning decoder never returns a
wrong string *provided the transmitted string is typical*.  Adversarial review
exposes the remaining loophole: an **atypical** source string `x ∉ S` can be
silently decoded to some typical `y ≠ x`, because the decoder has no way of
knowing that `x` was atypical.

Here we close that loophole with an independent random checksum
`C : α → Fin K` appended to the codeword (`log₂ K` extra bits).  The key point is
a *conditional independence* (fibrewise counting) argument: for a fixed hash
codebook `H` the candidate returned by the hash decoder is already determined,
so the checksum has only one chance in `K` of confirming it.

* `AlmostLossless.decodeChk_cost` — exact cost `|L| + 1` comparisons.
* `AlmostLossless.decodeChk_never_wrong` — typical strings are still never
  silently corrupted (deterministically).
* `AlmostLossless.silent_corruption_prob_le` — **for every source string, typical
  or not**, the probability of a silent corruption is at most `1 / K`.
-/

open AlmostLossless

open Finset

variable {α : Type*} [DecidableEq α] {M K : ℕ}

/-! ## 1. The checksummed scheme -/






/-! ## 2. The silent-corruption probability, uniformly over all sources -/

variable [Fintype α]

theorem AlmostLossless.card_silentSlice_mul_le(L : List α) (x : α) (H : α → Fin M) :
    K * (silentSlice L x H K).card ≤ K ^ Fintype.card α := by sorry
