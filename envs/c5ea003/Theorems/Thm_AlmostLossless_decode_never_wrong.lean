-- Prove2me | Theorems.Thm_AlmostLossless_decode_never_wrong
-- name    : AlmostLossless.decode_never_wrong
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:03:09.527585+00:00
-- url     : https://prove2.me/theorems/0931e551-8bd2-425c-ba9a-86d661cef5dc
-- title:
--   No silent corruption.
-- statement:
--   **No silent corruption.**  If the transmitted string `x` is a candidate, then
--   any output of the decoder is *exactly* `x`; a failure can only manifest as `none`,
--   never as a wrong string.
--
--   ```lean
--   theorem AlmostLossless.decode_never_wrong{L : List α} {H : α → Fin M} {x y : α}
--       (hx : x ∈ L) (h : (decode L H (H x)).1 = some y) : y = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/AlmostLosslessDecoder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/AlmostLosslessDecoder.lean#L110

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


omit [DecidableEq α] in

theorem AlmostLossless.decode_never_wrong{L : List α} {H : α → Fin M} {x y : α}
    (hx : x ∈ L) (h : (decode L H (H x)).1 = some y) : y = x := by sorry
