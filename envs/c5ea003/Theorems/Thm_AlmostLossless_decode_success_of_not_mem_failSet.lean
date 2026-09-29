-- Prove2me | Theorems.Thm_AlmostLossless_decode_success_of_not_mem_failSet
-- name    : AlmostLossless.decode_success_of_not_mem_failSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:00.868928+00:00
-- url     : https://prove2.me/theorems/f868f690-0751-45db-b6dc-6a1b891f986a
-- title:
--   Off the failure event the decoder returns the transmitted string, at a cost of
-- statement:
--   Off the failure event the decoder returns the transmitted string, at a cost of
--   exactly `|S|` hash comparisons.
--
--   ```lean
--   theorem AlmostLossless.decode_success_of_not_mem_failSet{S : Finset α} {L : List α} {x : α}
--       {H : α → Fin M} (hnd : L.Nodup) (hmem : ∀ y, y ∈ L ↔ y ∈ S)
--       (hx : x ∈ S) (hH : H ∉ failSet S x M) :
--       decode L H (H x) = (some x, L.length) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessDecoder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessDecoder.lean#L130

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

theorem AlmostLossless.decode_success_of_not_mem_failSet{S : Finset α} {L : List α} {x : α}
    {H : α → Fin M} (hnd : L.Nodup) (hmem : ∀ y, y ∈ L ↔ y ∈ S)
    (hx : x ∈ S) (hH : H ∉ failSet S x M) :
    decode L H (H x) = (some x, L.length) := by sorry
