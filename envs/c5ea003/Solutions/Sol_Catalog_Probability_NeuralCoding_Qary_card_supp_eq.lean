-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Qary.card_supp_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:46:59.590374+00:00
-- url     : https://prove2.me/submissions/df0a1e7c-7943-45fa-a9b0-35beb4b96a40

-- Sol generated from Probability/QaryNeuralCode.lean
import Mathlib
import Definitions.Def_Probability_QaryNeuralCode
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



omit [NeZero q] in
theorem mem_supp {c : QCode q N} {i : Fin N} : i ∈ supp c ↔ c i ≠ 0 := by
  simp [supp]















open Catalog.Probability.NeuralCoding.Qary in
theorem solution(S : Finset (Fin N)) :
    (univ.filter (fun c : QCode q N => supp c = S)).card = (q - 1) ^ S.card := by
  have hset : (univ.filter (fun c : QCode q N => supp c = S)) =
      Fintype.piFinset (fun i : Fin N => if i ∈ S then ({0}ᶜ : Finset (ZMod q)) else {0}) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hc i
      by_cases hi : i ∈ S
      · simp only [hi, if_true, Finset.mem_compl, Finset.mem_singleton]
        rw [← hc] at hi
        exact mem_supp.mp hi
      · simp only [hi, if_false, Finset.mem_singleton]
        by_contra hne
        exact hi (hc ▸ mem_supp.mpr hne)
    · intro hc
      ext i
      rw [mem_supp]
      have := hc i
      by_cases hi : i ∈ S
      · simp only [hi, if_true, Finset.mem_compl, Finset.mem_singleton] at this
        simp [hi, this]
      · simp only [hi, if_false, Finset.mem_singleton] at this
        simp [hi, this]
  rw [hset, Fintype.card_piFinset]
  have hcard : ∀ i : Fin N,
      (if i ∈ S then ({0}ᶜ : Finset (ZMod q)) else {0}).card
        = if i ∈ S then q - 1 else 1 := by
    intro i
    by_cases hi : i ∈ S <;> simp [hi, Finset.card_compl, ZMod.card]
  rw [Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_ite_mem, Finset.prod_const]
  congr 1
  simp
