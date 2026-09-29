-- Prove2me | solution 1 for PRNGSeed.seedCompressible_iff_decodable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:54:48.687171+00:00
-- url     : https://prove2.me/submissions/a170d841-ad9b-499b-88c1-f3fa4105856b

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





lemma seedProgram_getD_left {L : ℕ} (c init : Fin L → Bool) (j : Fin L) :
    (seedProgram c init).getD (j : ℕ) false = c j := by
  have hj : (j : ℕ) < (List.ofFn c).length := by simp
  simp [seedProgram, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma seedProgram_getD_right {L : ℕ} (c init : Fin L → Bool) (j : Fin L) :
    (seedProgram c init).getD (L + (j : ℕ)) false = init j := by
  have hj : (List.ofFn c).length ≤ L + (j : ℕ) := by simp
  simp [seedProgram, List.getD_eq_getElem?_getD]

lemma lfsrDecoder_seedProgram (N : ℕ) {L : ℕ} (c init : Fin L → Bool) :
    lfsrDecoder N L (seedProgram c init) = fun i : Fin N => lfsrBits L c init (i : ℕ) := by
  funext i
  simp only [lfsrDecoder, seedProgram_getD_left, seedProgram_getD_right]



/-! ### How much data can possibly be seed-compressible -/







/-! ### A concrete corpus: periodic files are seed-compressible -/



/-! ### Sample complexity of detection over `GF(2)` -/





/-! ### Routing: the two boxes do not cover the space -/




open PRNGSeed in
theorem solution(N L : ℕ) (w : Bits N) :
    IsSeedCompressible N L w ↔ ∃ p : List Bool, lfsrDecoder N L p = w := by
  constructor
  · rintro ⟨c, init, h⟩
    refine ⟨seedProgram c init, ?_⟩
    rw [lfsrDecoder_seedProgram]
    funext i
    exact (h i).symm
  · rintro ⟨p, hp⟩
    refine ⟨fun j : Fin L => p.getD (j : ℕ) false,
      fun j : Fin L => p.getD (L + (j : ℕ)) false, fun i => ?_⟩
    rw [← hp]
    rfl
