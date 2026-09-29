-- Prove2me | solution 1 for NeuralSparseCode.oneHot_attains_disjoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:03:30.531708+00:00
-- url     : https://prove2.me/submissions/d6af258a-36cd-4199-8730-e27056455fa3

-- Sol generated from Novelty/NeuralCodeSparsePacking.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeSparsePacking

/-!
# Sparse Neural Codes: Packing Bounds for Cell Assemblies

Cortical codes are **sparse**: a concept is represented by a small *assembly* of
`w` simultaneously active neurons out of `N`.  This file bounds how many
assemblies a population can host once we require them to overlap only a little,
which is what makes them separately readable.

## Model

A **neural code** on `N` neurons is a binary pattern `NeuralCode N = Fin N → Bool`
with **support** `supp c` (the active neurons) and **weight** `wt c = |supp c|`.
A **`w`-sparse codebook** is a finite set of patterns all of weight `w`.

## Main results

* `dist_add_two_mul_inter` — the exact relation between Hamming distance and
  overlap: `hammingDist x y + 2 |supp x ∩ supp y| = wt x + wt y`.
* `sparse_packing_bound` — **assembly packing bound**: if the assemblies of a
  `w`-sparse codebook pairwise overlap in fewer than `s` neurons then
  `|C| * C(w,s) ≤ C(N,s)`.  Each codeword privately owns all `C(w,s)` of its
  `s`-element subsets.
* `sparse_distance_bound` — the same bound expressed through the minimum Hamming
  distance (a Johnson-type bound): distance `≥ 2(w - s + 1)` suffices.
* `disjoint_assemblies_bound` — the case `s = 1`: pairwise disjoint assemblies of
  size `w` number at most `N / w` (stated as `|C| * w ≤ N`).
* `oneHot_attains_disjoint_bound` — that bound is attained at `w = 1` by the `N`
  grandmother cells, so it cannot be improved in general.
* `sparse_capacity_le_choose` — a `w`-sparse codebook never exceeds `C(N,w)`
  patterns, with equality for the full weight-`w` layer
  (`card_sparse_layer`).
-/

open NeuralSparseCode

open Finset









/-! ## Tightness -/


lemma supp_oneHot {N : ℕ} (i : Fin N) : supp (oneHot i) = {i} := by
  ext j; simp [supp, oneHot]

lemma wt_oneHot {N : ℕ} (i : Fin N) : wt (oneHot i) = 1 := by
  rw [wt, supp_oneHot, Finset.card_singleton]


/-! ## The full sparse layer -/




open NeuralSparseCode in
theorem solution(N : ℕ) :
    ((Finset.univ : Finset (Fin N)).image oneHot).card * 1 = N ∧
      (∀ x ∈ (Finset.univ : Finset (Fin N)).image oneHot, wt x = 1) ∧
      (∀ x ∈ (Finset.univ : Finset (Fin N)).image oneHot,
        ∀ y ∈ (Finset.univ : Finset (Fin N)).image oneHot, x ≠ y → Disjoint (supp x) (supp y)) := by
  have hinj : Function.Injective (oneHot (N := N)) := by
    intro i j hij
    have h := congrFun hij j
    simp only [oneHot, decide_eq_decide, iff_true] at h
    exact h.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, mul_one]
  · rintro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    exact wt_oneHot i
  · rintro x hx y hy hxy
    simp only [Finset.mem_image] at hx hy
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, rfl⟩ := hy
    rw [supp_oneHot, supp_oneHot, Finset.disjoint_singleton]
    intro h; exact hxy (by rw [h])
