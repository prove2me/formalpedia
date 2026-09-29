-- Prove2me | solution 1 for PRNGSeed.classifier_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:52:01.921978+00:00
-- url     : https://prove2.me/submissions/99a7bb49-a5a8-4804-b9ea-0abeda8171f8

-- Sol generated from MachineLearning/PRNGSeedDetection.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGSeedDetection
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
import Theorems.Thm_PRNGCompression_KC_compressible_count
import Theorems.Thm_PRNGCompression_card_bits
import Theorems.Thm_PRNGSeed_card_seedCompressible_le
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
theorem solution{N : ℕ} (L d : ℕ) (D : List Bool → Bits N)
    (hD : Function.Surjective D)
    (hbudget : 2 ^ d * 2 ^ (2 * L) + 2 ^ (N + 1) < 2 ^ d * 2 ^ N) :
    ∃ w : Bits N, ¬ IsSeedCompressible N L w ∧ ¬ (KC D w + d ≤ N) := by
  classical
  set A := seedCompressibleFinset N L with hA
  set B := univ.filter (fun w : Bits N => KC D w + d ≤ N) with hB
  have hcardA : A.card ≤ 2 ^ (2 * L) := by
    have h4 : (4 : ℕ) ^ L = 2 ^ (2 * L) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, mul_comm]
    rw [hA, ← h4]
    exact card_seedCompressible_le N L
  have hcardB : 2 ^ d * B.card ≤ 2 ^ (N + 1) := KC_compressible_count d D hD
  have hlt : (A ∪ B).card < (univ : Finset (Bits N)).card := by
    have h1 : (A ∪ B).card ≤ A.card + B.card := card_union_le _ _
    have h2 : 2 ^ d * (A.card + B.card) < 2 ^ d * 2 ^ N := by
      calc 2 ^ d * (A.card + B.card) = 2 ^ d * A.card + 2 ^ d * B.card := by ring
        _ ≤ 2 ^ d * 2 ^ (2 * L) + 2 ^ (N + 1) := by
            exact Nat.add_le_add (Nat.mul_le_mul_left _ hcardA) hcardB
        _ < 2 ^ d * 2 ^ N := hbudget
    have h3 : A.card + B.card < 2 ^ N :=
      lt_of_mul_lt_mul_left h2 (Nat.zero_le _)
    rw [card_univ, card_bits]
    omega
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨w, fun hs => hw ?_, fun hk => hw ?_⟩
  · refine mem_union_left _ ?_
    rw [hA]
    simp only [seedCompressibleFinset, mem_filter]
    exact ⟨mem_univ _, hs⟩
  · refine mem_union_right _ ?_
    rw [hB]
    simp only [mem_filter]
    exact ⟨mem_univ _, hk⟩
