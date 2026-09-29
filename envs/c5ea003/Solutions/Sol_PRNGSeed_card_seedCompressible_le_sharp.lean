-- Prove2me | solution 1 for PRNGSeed.card_seedCompressible_le_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:52:00.8175+00:00
-- url     : https://prove2.me/submissions/46933653-0c4d-4f37-af04-dd26c38b8d9e

-- Sol generated from MachineLearning/PRNGSeedDetection.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGBerlekampMassey
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGSeedDetection
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
import Theorems.Thm_PRNGSeed_lfsrRun_zero_seed
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



@[simp] lemma lfsrBits_zero_seed (L : ℕ) (c : Fin L → Bool) (n : ℕ) :
    lfsrBits L c (fun _ => false) n = false := by
  have h : (fun i : Fin L => toZ2 ((fun _ => false : Fin L → Bool) i)) = fun _ => (0 : ZMod 2) := by
    funext i; simp [toZ2]
  rw [lfsrBits, h, lfsrRun_zero_seed]
  decide




/-! ### A concrete corpus: periodic files are seed-compressible -/



/-! ### Sample complexity of detection over `GF(2)` -/





/-! ### Routing: the two boxes do not cover the space -/




open PRNGSeed in
-- open removed: section is not a namespace
theorem solution(N L : ℕ) :
    (seedCompressibleFinset N L).card + 2 ^ L ≤ 4 ^ L + 1 := by
  classical
  set A : Finset ((Fin L → Bool) × (Fin L → Bool)) :=
    univ.filter (fun t => t.2 ≠ fun _ => false) with hAdef
  set f : (Fin L → Bool) × (Fin L → Bool) → Bits N :=
    fun t => (fun i : Fin N => lfsrBits L t.1 t.2 (i : ℕ)) with hf
  set z : Bits N := (fun _ => false) with hz
  have hsub : seedCompressibleFinset N L ⊆ insert z (A.image f) := by
    intro w hw
    simp only [seedCompressibleFinset, mem_filter] at hw
    obtain ⟨c, init, hci⟩ := hw.2
    by_cases h0 : init = fun _ => false
    · have hwz : w = z := by
        funext i
        rw [hci i, h0, hz]
        exact lfsrBits_zero_seed L c (i : ℕ)
      rw [hwz]
      exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_image.mpr ⟨(c, init), ?_, ?_⟩)
      · simp only [hAdef, mem_filter]
        exact ⟨mem_univ _, h0⟩
      · exact funext fun i => (hci i).symm
  have hcardA : A.card + 2 ^ L = 4 ^ L := by
    have hcompl :
        (univ.filter
            (fun t : (Fin L → Bool) × (Fin L → Bool) => ¬ (t.2 ≠ fun _ => false)))
          = univ ×ˢ ({fun _ => false} : Finset (Fin L → Bool)) := by
      ext t
      constructor
      · intro ht
        simp only [mem_filter, not_not] at ht
        exact Finset.mem_product.mpr ⟨mem_univ _, mem_singleton.mpr ht.2⟩
      · intro ht
        have h2 := (Finset.mem_product.mp ht).2
        simp only [mem_filter, mem_univ, true_and, not_not]
        exact mem_singleton.mp h2
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset ((Fin L → Bool) × (Fin L → Bool))))
      (p := fun t => t.2 ≠ fun _ => false)
    rw [hcompl, Finset.card_product] at hsplit
    have hcard : (univ : Finset ((Fin L → Bool) × (Fin L → Bool))).card = 4 ^ L := by
      rw [card_univ]
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
    have hcu : (univ : Finset (Fin L → Bool)).card = 2 ^ L := by
      rw [card_univ]
      simp
    rw [hcu, hcard] at hsplit
    simpa [hAdef] using hsplit
  have h1 : (seedCompressibleFinset N L).card ≤ A.card + 1 := by
    refine le_trans (card_le_card hsub) ?_
    refine le_trans (card_insert_le _ _) ?_
    exact Nat.succ_le_succ card_image_le
  omega
