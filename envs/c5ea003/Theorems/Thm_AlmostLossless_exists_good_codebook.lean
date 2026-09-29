-- Prove2me | Theorems.Thm_AlmostLossless_exists_good_codebook
-- name    : AlmostLossless.exists_good_codebook
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:49.802884+00:00
-- url     : https://prove2.me/theorems/211564fa-274e-411e-8736-5383e567ac7f
-- title:
--   Existence of a good deterministic codebook (derandomised random coding):
-- statement:
--   **Existence of a good deterministic codebook** (derandomised random coding):
--   some codebook with `M` codewords is ambiguous on at most `|S|(|S|-1)/M` of the
--   typical strings.  In particular with `M ≥ |S|/ε` at most `ε|S|` typical strings
--   are lost, while the code length stays `log₂ M`.
--
--   ```lean
--   theorem AlmostLossless.exists_good_codebook(S : Finset α) (hM : 0 < M) :
--       ∃ H : α → Fin M, M * (badStrings S H).card ≤ S.card * (S.card - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessDecoder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessDecoder.lean#L264

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






/-! ## 5. Derandomisation: a single good codebook exists -/

theorem AlmostLossless.exists_good_codebook(S : Finset α) (hM : 0 < M) :
    ∃ H : α → Fin M, M * (badStrings S H).card ≤ S.card * (S.card - 1) := by sorry
