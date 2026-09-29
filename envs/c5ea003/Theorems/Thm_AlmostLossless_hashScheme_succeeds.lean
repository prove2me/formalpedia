-- Prove2me | Theorems.Thm_AlmostLossless_hashScheme_succeeds
-- name    : AlmostLossless.hashScheme_succeeds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:07:28.921579+00:00
-- url     : https://prove2.me/theorems/88f7092f-5655-4d58-88bc-f1f70cb56144
-- title:
--   Codebook symbols that do not collide are decoded exactly.
-- statement:
--   Codebook symbols that do not collide are decoded exactly.
--
--   ```lean
--   theorem AlmostLossless.hashScheme_succeeds{l : List α} {h : α → Fin M} {x : α}
--       (hnd : l.Nodup) (hx : x ∈ l)
--       (hnc : ¬ ∃ y ∈ l.toFinset, y ≠ x ∧ h y = h x) :
--       (hashScheme l h).Succeeds x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessRandomCoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessRandomCoding.lean#L292

-- Thm stub generated from Bridges/AlmostLosslessRandomCoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression II: Random Coding with a Certified Decoder

## Bridge: Universal hashing (algebra) ↔ Shannon random coding (probability)
##         ↔ Verified algorithmics (exact decoder cost)

Shannon's random-coding argument is usually stated with an *unbounded* random
codebook and an existential (non-constructive) decoder.  Here everything is
finite, explicit and cost-instrumented:

* the "random codebook" is a **2-universal hash family** `H : Fin K → α → Fin M`
  (`Universal2`), so the randomness is a single key `k ∈ Fin K`;
* the decoder `decodeList` scans an explicit codebook list `l` and answers
  `some x` **only** when the match is unique;
* the scan is instrumented (`scanCost`) so the decoding cost is *proved*, not
  estimated: exactly `l.length` hash evaluations per query.

Main results:

* `sum_collision_mass_le` — the averaging (first-moment) identity behind random
  coding, in the exact form `M · Σₖ P(collision) ≤ K · |S| · P(A)`;
* `exists_good_key` — derandomized existence of a single good key;
* `decodeList_eq_some_of_unique`, `not_silentError_of_mem` — the decoder never
  corrupts a codebook symbol silently;
* `exists_almost_lossless_scheme` — **the deliverable**: a key `k` such that the
  scheme fails with probability `≤ δ + |S|/M`, corrupts silently with
  probability `≤ |S|/M`, and costs exactly `|S|` steps per decode;
* `converse_flat_source` — the matching converse, giving a rate gap independent
  of the source size.

## Impact: almost_lossless_achievability, certified_decoder_cost
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless

/-! ## Section 1: Universal hash families and collisions -/


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}








/-! ## Section 2: The first-moment (random coding) bound -/




/-! ## Section 3: The cost-instrumented decoder -/


variable {α : Type*} {M : ℕ}











/-! ## Section 4: The almost-lossless scheme and its guarantees -/


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}


omit [Fintype α] in

theorem AlmostLossless.hashScheme_succeeds{l : List α} {h : α → Fin M} {x : α}
    (hnd : l.Nodup) (hx : x ∈ l)
    (hnc : ¬ ∃ y ∈ l.toFinset, y ≠ x ∧ h y = h x) :
    (hashScheme l h).Succeeds x := by sorry
