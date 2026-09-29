-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Qary.qary_hamming_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:56:05.655127+00:00
-- url     : https://prove2.me/submissions/df70f8e7-ff5d-4881-83b7-939b3df4ccbd

-- Sol generated from Probability/QaryNeuralCode.lean
import Mathlib
import Definitions.Def_Probability_QaryNeuralCode
import Theorems.Thm_Catalog_Probability_NeuralCoding_Qary_card_ball
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Neural codes over a finite alphabet: capacity, energy classes and noisy decoding

`Catalog/Novelty/NeuralCoding.lean` models a neural code as a *binary* activity
pattern `Fin N → Bool`, with capacity `2 ^ N`.  Real neurons emit a graded
number of spikes in a window, so this file replaces the binary alphabet by an
arbitrary finite alphabet of size `q` (represented as `ZMod q`, which supplies
the group structure needed for translation arguments), `0` meaning *silent*.

## Results

1. `card_qCode` — **capacity `q ^ N`.**  There are exactly `q ^ N` patterns; and
   `qary_capacity_bound` turns this into a bound on the number of distinguishable
   concepts.
2. `card_supp_eq` — the number of patterns with a *prescribed* support `S` is
   `(q - 1) ^ |S|`.
3. `card_weight_eq` — the **type class** of energy exactly `k` has
   `N.choose k * (q - 1) ^ k` members, generalising the binary `N.choose k`.
4. `card_weight_le` — the **energy-constrained capacity**: at most `k` active
   neurons gives exactly `∑_{j ≤ k} N.choose j * (q - 1) ^ j` patterns.
5. `hammingDist_eq_weight_sub`, `card_ball` — Hamming balls have the same volume
   as the energy-`≤ r` class, by translation invariance.
6. `qary_unique_decoding` — **decoding guarantee.**  A codebook of minimum
   distance `≥ 2t + 1` decodes uniquely from any received pattern within `t`
   corrupted neurons.
7. `qary_hamming_bound` — **sphere packing.**  Such a codebook has at most
   `q ^ N / ∑_{j ≤ t} N.choose j (q-1)^j` codewords.
8. `binary_specialisation` — for `q = 2` the type-class count reduces to the
   binary count `N.choose k` of the original file.
-/

open Catalog.Probability.NeuralCoding.Qary

open Finset


variable {q N : ℕ} [NeZero q]




/-- **Capacity of a `q`-ary population**: exactly `q ^ N` patterns. -/
theorem card_qCode (q N : ℕ) [NeZero q] : Fintype.card (QCode q N) = q ^ N := by
  simp [QCode, ZMod.card]








omit [NeZero q] in
/-- **Unique decoding.**  If two codewords are at distance at least `2t + 1`
whenever distinct, then a received pattern within `t` corruptions of a codeword
determines that codeword. -/
theorem qary_unique_decoding {t : ℕ} {C : Finset (QCode q N)}
    (hmin : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y)
    {x c₁ c₂ : QCode q N} (h₁ : c₁ ∈ C) (h₂ : c₂ ∈ C)
    (hd₁ : hammingDist x c₁ ≤ t) (hd₂ : hammingDist x c₂ ≤ t) : c₁ = c₂ := by
  by_contra hne
  have htri : hammingDist c₁ c₂ ≤ hammingDist c₁ x + hammingDist x c₂ :=
    hammingDist_triangle c₁ x c₂
  have h1 : hammingDist c₁ x = hammingDist x c₁ := hammingDist_comm c₁ x
  have := hmin c₁ h₁ c₂ h₂ hne
  omega

/-- Balls of radius `t` around the codewords of a code with minimum distance
`≥ 2t + 1` are pairwise disjoint. -/
theorem balls_pairwiseDisjoint {t : ℕ} {C : Finset (QCode q N)}
    (hmin : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y) :
    (C : Set (QCode q N)).PairwiseDisjoint (fun c => ball c t) := by
  intro c₁ h₁ c₂ h₂ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [ball, mem_filter, mem_univ, true_and] at hx₁ hx₂
  exact hne (qary_unique_decoding hmin h₁ h₂ hx₁ hx₂)





open Catalog.Probability.NeuralCoding.Qary in
theorem solution{t : ℕ} (C : Finset (QCode q N))
    (hmin : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 2 * t + 1 ≤ hammingDist x y) :
    C.card * (∑ j ∈ range (t + 1), N.choose j * (q - 1) ^ j) ≤ q ^ N := by
  classical
  have hdisj := balls_pairwiseDisjoint hmin
  have hunion : (C.biUnion (fun c => ball c t)).card = ∑ c ∈ C, (ball c t).card :=
    Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)
  have hsum : ∑ c ∈ C, (ball c t).card
      = C.card * (∑ j ∈ range (t + 1), N.choose j * (q - 1) ^ j) := by
    rw [Finset.sum_congr rfl (fun c _ => card_ball c t), Finset.sum_const,
      smul_eq_mul]
  have hle : (C.biUnion (fun c => ball c t)).card ≤ Fintype.card (QCode q N) :=
    Finset.card_le_univ _
  rw [card_qCode] at hle
  rw [← hsum, ← hunion]
  exact hle
