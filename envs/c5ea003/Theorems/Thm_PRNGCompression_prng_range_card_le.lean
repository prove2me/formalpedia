-- Prove2me | Theorems.Thm_PRNGCompression_prng_range_card_le
-- name    : PRNGCompression.prng_range_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:46:08.641227+00:00
-- url     : https://prove2.me/theorems/bab4eb0c-b48a-4cad-92c0-88e3a56d5983
-- title:
--   The output set of a PRNG has at most `2 ^ s` elements.
-- statement:
--   The output set of a PRNG has at most `2 ^ s` elements.
--
--   ```lean
--   theorem PRNGCompression.prng_range_card_le{n s : ℕ} (G : Bits s → Bits n) :
--       (univ.image G).card ≤ 2 ^ s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGCompressionBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGCompressionBound.lean#L107

-- Thm stub generated from MachineLearning/PRNGCompressionBound.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# PRNGs Cannot Beat the Pigeonhole Bound

A formal negative result for the research question *"can a pseudo-random number
generator help compress arbitrary data?"*.  The answer is **no**, and this file
proves it in several independent, quantitative ways, together with a fully
formal "demo": a concrete hybrid compressor built on top of a PRNG which
genuinely compresses every PRNG output to `s + 1` bits, while some string still
provably needs `n` bits, and the compressible strings form a `2 ^ (s+2-n)`
fraction of all strings.

## Central Idea

A PRNG is a *function* `G : seeds → streams`.  Functions do not create
information: `2 ^ s` seeds produce at most `2 ^ s` streams.  Any decompressor —
PRNG-driven or not — is just a map `List Bool → data`, so the counting bounds of
`MachineLearning.PRNGCompressionCore` apply verbatim.  A PRNG therefore only
compresses data that *was already* of low description complexity; it never
enlarges the set of `k`-bit-describable strings beyond `2 ^ (k+1)`.

## Main Definitions

* `KC D x` — description complexity of `x` relative to the decompressor `D`
  (length of the shortest program `p` with `D p = x`)
* `hybridDecoder G` — the "PRNG demo" decompressor: a `false` flag selects
  *seed mode* (run the PRNG on the following `s` bits), a `true` flag selects
  *literal mode* (copy the following `n` bits)

## Main Results

Pure PRNG (no side information):

* `prng_seed_bits_lower_bound` — a surjective PRNG needs `s ≥ n` seed bits
* `exists_unreachable_of_short_seed` — if `s < n` some string is never produced
* `prng_range_density` — the PRNG's output set covers at most a `2 ^ (s-n)`
  fraction of all `n`-bit strings

PRNG plus arbitrary side information (this kills the "seed + patch" idea):

* `prng_assisted_no_gain` — for *any* seed-indexed decoder family and *any*
  encoder, some string needs `s + |program| ≥ n` total bits

Complexity-theoretic form:

* `exists_KC_ge` — for every decompressor, some `n`-bit string has `KC ≥ n`
* `KC_compressible_count` — at most a `2 ^ (1-d)` fraction of strings have
  `KC ≤ n - d`
* `KC_postprocess_le` — running a PRNG after a decoder never *increases*
  complexity (data processing), yet the counting bound is unchanged

The demo (both sides of the coin, formally):

* `KC_hybrid_prng_output_le` — every PRNG output compresses to `s + 1` bits
* `KC_hybrid_le_succ` — nothing ever blows up: `KC ≤ n + 1` for all strings
* `prng_no_free_lunch` — yet if `s + 1 < n` there is a string with `KC ≥ n`,
  and that string is provably not a PRNG output
* `lcg_image_card_le`, `lcg_missing_count` — a concrete 4-bit-seed LCG whose
  `8`-bit outputs hit exactly `16` of the `256` values (`240` are unreachable)

## Application Keywords

pseudo-random number generator, Kolmogorov complexity, incompressibility,
pigeonhole principle, lossless compression, no free lunch, seed search
-/


open Finset

open PRNGCompression

/-! ## Seeds as bit strings -/






/-! ## A pure PRNG: no side information -/

theorem PRNGCompression.prng_range_card_le{n s : ℕ} (G : Bits s → Bits n) :
    (univ.image G).card ≤ 2 ^ s := by sorry
