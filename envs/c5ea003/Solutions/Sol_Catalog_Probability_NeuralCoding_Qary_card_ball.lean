-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Qary.card_ball
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:53:44.144653+00:00
-- url     : https://prove2.me/submissions/f7a82225-9e58-4b05-b5c9-d7abfa3eee26

-- Sol generated from Probability/QaryNeuralCode.lean
import Mathlib
import Definitions.Def_Probability_QaryNeuralCode
import Theorems.Thm_Catalog_Probability_NeuralCoding_Qary_card_weight_le
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
/-- Hamming distance is the weight of the difference: translation invariance of
the `q`-ary code space. -/
theorem hammingDist_eq_weight_sub (x y : QCode q N) :
    hammingDist x y = weight (x - y) := by
  simp only [hammingDist, weight, supp]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [sub_eq_zero]









open Catalog.Probability.NeuralCoding.Qary in
theorem solution(c : QCode q N) (r : ℕ) :
    (ball c r).card = ∑ j ∈ range (r + 1), N.choose j * (q - 1) ^ j := by
  classical
  rw [← card_weight_le (q := q) (N := N) r]
  refine Finset.card_nbij' (fun x => x - c) (fun y => y + c) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [ball, Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
    rwa [← hammingDist_eq_weight_sub]
  · intro y hy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hy
    simp only [ball, Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and]
    rw [hammingDist_eq_weight_sub]
    simpa using hy
  · intro x _; simp
  · intro y _; simp
