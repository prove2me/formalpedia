-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Qary.card_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:51:51.438579+00:00
-- url     : https://prove2.me/submissions/a2a90667-70b9-4334-a5b4-1fb648de4d46

-- Sol generated from Probability/QaryNeuralCode.lean
import Mathlib
import Definitions.Def_Probability_QaryNeuralCode
import Theorems.Thm_Catalog_Probability_NeuralCoding_Qary_card_weight_eq
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


















open Catalog.Probability.NeuralCoding.Qary in
theorem solution(k : ℕ) :
    (univ.filter (fun c : QCode q N => weight c ≤ k)).card
      = ∑ j ∈ range (k + 1), N.choose j * (q - 1) ^ j := by
  classical
  have hmaps : Set.MapsTo (fun c : QCode q N => weight c)
      ↑(univ.filter (fun c : QCode q N => weight c ≤ k)) ↑(range (k + 1)) := by
    intro c hc
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hc
    simp only [Finset.mem_coe, mem_range]
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using mem_range.mp hj
  have hEq : ({c ∈ univ.filter (fun c : QCode q N => weight c ≤ k) | weight c = j})
      = univ.filter (fun c : QCode q N => weight c = j) := by
    ext c
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by omega, h⟩
  rw [hEq, card_weight_eq]
