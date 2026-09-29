-- Prove2me | solution 1 for PRNGCompression.exists_shortest_code
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:33:25.716332+00:00
-- url     : https://prove2.me/submissions/5a2da8af-e13c-44e8-b2f0-40f5cce217c4

-- Sol generated from MachineLearning/PRNGCompressionBound.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Theorems.Thm_PRNGCompression_exists_shortest_program
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





/-! ## A PRNG with arbitrary side information -/


/-! ## Description complexity relative to a decompressor -/








/-! ## The demo: a PRNG-powered compressor that works exactly where it must -/







/-! ## Concrete demo: a 4-bit-seed linear congruential generator -/








open PRNGCompression in
theorem solution{n : ℕ} (D : List Bool → Bits n) (hD : Function.Surjective D) :
    ∃ c : Bits n → List Bool, Function.Injective c ∧ ∀ x, (c x).length = KC D x ∧ D (c x) = x := by
  have hall : ∀ x : Bits n, ∃ p : List Bool, p.length = KC D x ∧ D p = x := by
    intro x
    exact exists_shortest_program (hD x)
  choose c hc1 hc2 using hall
  refine ⟨c, ?_, fun x => ⟨hc1 x, hc2 x⟩⟩
  intro x y hxy
  have := hc2 x
  rw [hxy, hc2 y] at this
  exact this.symm
