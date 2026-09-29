-- Prove2me | Theorems.Thm_AlmostLossless_success_prob_ge
-- name    : AlmostLossless.success_prob_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:04:16.640962+00:00
-- url     : https://prove2.me/theorems/0f8f50a0-cc0e-4d46-9010-a8e19008fa51
-- title:
--   Almost-lossless guarantee, real-valued form.
-- statement:
--   **Almost-lossless guarantee, real-valued form.**  If the codebook has
--   `M ≥ (|S| - 1)/ε` entries, then a uniformly random codebook decodes a fixed
--   typical string correctly with probability at least `1 - ε`.
--
--   Note the rate: `log₂ M ≈ log₂ |S| + log₂(1/ε)` bits, versus the pigeonhole
--   requirement `log₂ |α|` bits for exact decoding of *every* string.
--
--   ```lean
--   theorem AlmostLossless.success_prob_ge{S : Finset α} {L : List α} (hnd : L.Nodup)
--       (hmem : ∀ y, y ∈ L ↔ y ∈ S) {x : α} (hx : x ∈ S) (hM : 0 < M)
--       {ε : ℝ} (hε : 0 < ε) (hMe : ((S.card : ℝ) - 1) / ε ≤ M) :
--       1 - ε ≤ ((goodSet L x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessDecoder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessDecoder.lean#L217

-- Thm stub generated from Geometry/AlmostLosslessDecoder.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# Almost-lossless compression: an explicit decoder, its cost, and its failure probability

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

The scheme.  Fix a *typical set* `S : Finset α` (the strings the source actually
produces with high probability), enumerated as a duplicate-free candidate list
`L`, and a codebook `H : α → Fin M` drawn uniformly at random.  The encoder sends
`H x` (`⌈log₂ M⌉` bits).  The decoder scans `L`, collects all `y` with
`H y = H x`, and

* outputs `some y` **only** when that list is a singleton, and
* outputs `none` otherwise.

Main results:

* `AlmostLossless.decode_cost` — the decoder performs **exactly `|L|`** hash
  comparisons (an exact complexity figure, not an asymptotic one).
* `AlmostLossless.decode_never_wrong` — *no silent corruption*: whenever the
  decoder outputs a string, that string is the transmitted one.  Errors are
  always reported as `none`.
* `AlmostLossless.decode_success_of_not_mem_failSet` — the decoder succeeds
  unless the codebook collides on the typical set.
* `AlmostLossless.failSet_prob_le` / `AlmostLossless.success_prob_ge` — the
  Shannon random-coding bound in exact counting form and in ℝ:
  `P[failure] ≤ (|S| - 1)/M`, hence `P[success] ≥ 1 - ε` as soon as
  `M ≥ (|S| - 1)/ε`.
* `AlmostLossless.exists_good_codebook` — derandomisation: some *fixed*
  codebook of size `M` fails on at most `|S|(|S|-1)/M` typical strings.
-/

open AlmostLossless

open Finset

/-! ## 1. The scanning decoder and its exact cost -/

variable {α : Type*} [DecidableEq α] {M : ℕ}







/-! ## 2. No silent corruption -/



/-! ## 3. When does the decoder succeed? -/

variable [Fintype α]



/-! ## 4. The random-coding bound -/

theorem AlmostLossless.success_prob_ge{S : Finset α} {L : List α} (hnd : L.Nodup)
    (hmem : ∀ y, y ∈ L ↔ y ∈ S) {x : α} (hx : x ∈ S) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) (hMe : ((S.card : ℝ) - 1) / ε ≤ M) :
    1 - ε ≤ ((goodSet L x M).card : ℝ) / ((M : ℝ) ^ Fintype.card α) := by sorry
