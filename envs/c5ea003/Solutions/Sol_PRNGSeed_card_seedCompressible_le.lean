-- Prove2me | solution 1 for PRNGSeed.card_seedCompressible_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:45:07.526282+00:00
-- url     : https://prove2.me/submissions/b4b063ac-6436-435e-be63-c6adbade02a3

-- Sol generated from MachineLearning/PRNGSeedDetection.lean
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



/-! ### Sample complexity of detection over `GF(2)` -/





/-! ### Routing: the two boxes do not cover the space -/




open PRNGSeed in
-- open removed: section is not a namespace
theorem solution(N L : ℕ) :
    (seedCompressibleFinset N L).card ≤ 4 ^ L := by
  classical
  have hsub : seedCompressibleFinset N L ⊆
      (univ : Finset ((Fin L → Bool) × (Fin L → Bool))).image
        (fun t : (Fin L → Bool) × (Fin L → Bool) =>
          (fun i : Fin N => lfsrBits L t.1 t.2 (i : ℕ))) := by
    intro w hw
    simp only [seedCompressibleFinset, mem_filter] at hw
    obtain ⟨c, init, hci⟩ := hw.2
    refine mem_image.mpr ⟨(c, init), mem_univ _, ?_⟩
    funext i
    exact (hci i).symm
  refine le_trans (card_le_card hsub) (le_trans card_image_le ?_)
  rw [card_univ]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
