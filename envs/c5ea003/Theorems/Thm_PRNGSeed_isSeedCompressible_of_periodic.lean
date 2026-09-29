-- Prove2me | Theorems.Thm_PRNGSeed_isSeedCompressible_of_periodic
-- name    : PRNGSeed.isSeedCompressible_of_periodic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:47:37.256786+00:00
-- url     : https://prove2.me/theorems/53fb4727-b6c9-438d-87f4-1e5c5cab7e85
-- title:
--   Every periodic file is seed-compressible.
-- statement:
--   **Every periodic file is seed-compressible.**  A file of length `N` whose
--   bits depend only on the index modulo `p` is produced by the order-`p` register
--   with taps `(1,0,…,0)` — hence, by `KC_lfsrDecoder_le`, it has a `2p`-bit
--   description.  Periodic and run-structured data in real corpora therefore lands
--   in the seed-compressible box of the router.
--
--   ```lean
--   theorem PRNGSeed.isSeedCompressible_of_periodic{N p : ℕ} (hp : 0 < p) (w : Bits N)
--       (hper : ∀ i : Fin N, ∀ h : (i : ℕ) % p < N, w i = w ⟨(i : ℕ) % p, h⟩) :
--       IsSeedCompressible N p w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGSeedDetection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGSeedDetection.lean#L278

-- Thm stub generated from MachineLearning/PRNGSeedDetection.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGSeedDetection
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Detecting Seed-Compressible Files and Routing Them

This file joins the two halves of the "PRNG-generated real-world data" question:
the *seed-recovery* theory of `MachineLearning.PRNGSeedRecoveryLFSR` and the
*counting limits* of `MachineLearning.PRNGCompressionBound`.

A file is modelled as `Bits N` (an `N`-bit string).  It is **`L`-seed
compressible** when some binary LFSR of order `L` — that is, `2L` bits of taps
and seed — emits it verbatim.

## Main results

* `seedCompressible_iff_decodable` — **the falsifiability gate**: a file is
  `L`-seed compressible *iff* a `2L`-bit program makes the fixed decoder
  `lfsrDecoder` output the file exactly, bit for bit.
* `KC_lfsrDecoder_le` — detection pays: such a file has description complexity
  at most `2L`, independently of its length `N`.
* `card_seedCompressible_le` — at most `4 ^ L` of the `2 ^ N` files are `L`-seed
  compressible: the detector's search space, and its false-positive budget.
* `seedCompressible_rare` — the seed-compressible fraction is `2 ^ (2L - N)`.
* `exists_not_seedCompressible` — as soon as `2L < N` the detector must reject
  something, so the classifier is not vacuous.
* `classifier_dichotomy` — for any decoder `D` at all there are files that are
  *neither* seed-compressible *nor* `d`-bit compressible by `D`: the router's
  two boxes ("seed-compressible" / "model-compressible") do not cover the space.
* `not_seedCompressible_and_hard_64` — a concrete instance of the dichotomy at
  `N = 64`, `L = 8`, `d = 4`.
* `card_seedCompressible_le_sharp` — the naive `4 ^ L` count is never tight:
  all zero-seed registers collapse to the same file.
* `isSeedCompressible_of_periodic` — a real corpus that the detector does catch:
  every `p`-periodic file is seed compressible with a `2p`-bit description.
* `detector_sound_from_2L_bits`, `lfsrBits_eq_of_agree_two_mul` — a `2L`-bit
  observation window is enough: fitting `2L` bits of an `L`-seed-compressible
  file forces exact reproduction of the whole file.

## Application keywords

PRNG detection, seed recovery, LFSR fingerprinting, Kolmogorov complexity,
compression benchmark, classifier
-/


open Finset PRNGCompression

open PRNGSeed

/-! ### Bits versus `GF(2)` -/





/-! ### The detector and its decoder -/










/-! ### How much data can possibly be seed-compressible -/







/-! ### A concrete corpus: periodic files are seed-compressible -/

theorem PRNGSeed.isSeedCompressible_of_periodic{N p : ℕ} (hp : 0 < p) (w : Bits N)
    (hper : ∀ i : Fin N, ∀ h : (i : ℕ) % p < N, w i = w ⟨(i : ℕ) % p, h⟩) :
    IsSeedCompressible N p w := by sorry
