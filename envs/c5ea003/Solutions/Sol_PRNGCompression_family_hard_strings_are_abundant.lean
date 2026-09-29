-- Prove2me | solution 1 for PRNGCompression.family_hard_strings_are_abundant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:45:03.582152+00:00
-- url     : https://prove2.me/submissions/fe271395-9ba8-49be-a8be-79dcf2b95bbc

-- Sol generated from MachineLearning/PRNGCompressionUniversal.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
import Definitions.Def_MachineLearning_PRNGCompressionUniversal
import Theorems.Thm_PRNGCompression_KC_compressible_count
import Theorems.Thm_PRNGCompression_KC_le_of_decodes
import Theorems.Thm_PRNGCompression_bitsOfList_seedBits
import Theorems.Thm_PRNGCompression_exists_shortest_program
import Theorems.Thm_PRNGCompression_seedBits_length
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance and Uniform Hardness against a Whole Family of Generators

Third research cycle on top of `MachineLearning.PRNGCompressionBound` and
`MachineLearning.PRNGCompressionDepth`.

The previous cycles show that a *fixed* PRNG cannot help.  A natural retreat is:
*"then let me keep a library of `2 ^ m` generators and, for each file, use the
one that happens to fit"*.  This file closes that retreat in the strongest form:
there is a **single** string that is simultaneously hard for **every** member of
the library.

## Central Idea

Two standard ingredients, formalized from scratch:

* **Invariance.**  If a decompressor `D` can simulate `D'` after reading a fixed
  `q`-bit prefix, then `KC D x ≤ |q| + KC D' x` (`KC_le_of_simulates`).
* **A universal machine for a finite family.**  `familyDecoder F` reads `m` index
  bits and then runs `F i` on the rest; it satisfies
  `KC (familyDecoder F) x ≤ m + KC (F i) x` for every member `i`.

Applying the incompressibility theorem to `familyDecoder F` and pushing the
bound back through the members yields uniform hardness.

## Main Results

* `KC_le_of_simulates` — invariance theorem for description complexity
* `familyDecoder_surjective`, `KC_familyDecoder_le` — the universal machine
* `exists_hard_for_whole_family` — one string `x` with `n ≤ m + KC (F i) x`
  for *every* generator `i` in a library of `2 ^ m` generators
* `family_hard_strings_are_abundant` — such hard strings are not exceptional:
  strings that are easy for *some* member of the library number at most
  `2 ^ (m + s + 1)` when each member compresses to `s` bits

## Application Keywords

invariance theorem, universal decompressor, Kolmogorov complexity, generator
library, uniform incompressibility, compression lower bounds
-/


open Finset

open PRNGCompression

/-! ## Invariance -/

/-- **Invariance theorem.**  If `D` simulates `D'` after a fixed prefix `q`,
then complexities differ by at most `|q|`.  Choosing `D'` to be a PRNG-based
decompressor: switching to a PRNG changes description length only by the
constant needed to describe the PRNG. -/
theorem KC_le_of_simulates {X : Type*} (D D' : List Bool → X) (q : List Bool)
    (hsim : ∀ p, D (q ++ p) = D' p) (x : X) (h : ∃ p, D' p = x) :
    KC D x ≤ q.length + KC D' x := by
  obtain ⟨p, hlen, hdec⟩ := exists_shortest_program h
  have hD : D (q ++ p) = x := by rw [hsim p, hdec]
  have := KC_le_of_decodes hD
  simp only [List.length_append] at this
  omega

/-! ## A universal machine for a library of `2 ^ m` decompressors -/


lemma familyDecoder_apply {n m : ℕ} (F : Bits m → List Bool → Bits n)
    (i : Bits m) (p : List Bool) :
    familyDecoder F (seedBits i ++ p) = F i p := by
  have h1 : (seedBits i ++ p).take m = seedBits i := List.take_left' (by simp)
  have h2 : (seedBits i ++ p).drop m = p := List.drop_left' (by simp)
  simp [familyDecoder, h1, h2]

/-- Naming a member of the library costs exactly `m` bits, never more. -/
theorem KC_familyDecoder_le {n m : ℕ} (F : Bits m → List Bool → Bits n)
    (i : Bits m) (x : Bits n) (h : ∃ p, F i p = x) :
    KC (familyDecoder F) x ≤ m + KC (F i) x := by
  have hsim : ∀ p, familyDecoder F (seedBits i ++ p) = F i p := familyDecoder_apply F i
  have := KC_le_of_simulates (familyDecoder F) (F i) (seedBits i) hsim x h
  simpa using this

theorem familyDecoder_surjective {n m : ℕ} (F : Bits m → List Bool → Bits n)
    (i : Bits m) (hi : Function.Surjective (F i)) :
    Function.Surjective (familyDecoder F) := by
  intro x
  obtain ⟨p, hp⟩ := hi x
  exact ⟨seedBits i ++ p, by rw [familyDecoder_apply F i p, hp]⟩




open PRNGCompression in
theorem solution{n m s : ℕ} (F : Bits m → List Bool → Bits n)
    (hF : ∀ i, Function.Surjective (F i)) (hms : m + s + 1 ≤ n) :
    2 ^ (n - (m + s)) *
        (univ.filter (fun x : Bits n => ∃ i, KC (F i) x ≤ s)).card ≤ 2 ^ (n + 1) := by
  classical
  have hsub :
      (univ.filter (fun x : Bits n => ∃ i, KC (F i) x ≤ s))
        ⊆ (univ.filter (fun x : Bits n =>
            KC (familyDecoder F) x + (n - (m + s)) ≤ n)) := by
    intro x hx
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hx).2
    have hle := KC_familyDecoder_le F i x (hF i x)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
  have hcount := KC_compressible_count (n := n) (n - (m + s)) (familyDecoder F)
      (familyDecoder_surjective F (fun _ => false) (hF (fun _ => false)))
  exact le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)) hcount
