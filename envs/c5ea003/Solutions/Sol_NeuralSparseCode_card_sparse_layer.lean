-- Prove2me | solution 1 for NeuralSparseCode.card_sparse_layer
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:03:29.027677+00:00
-- url     : https://prove2.me/submissions/5b0a76d2-9067-400e-82ac-25516657fe71

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





/-! ## The full sparse layer -/




open NeuralSparseCode in
theorem solution(N w : ℕ) :
    (Finset.univ.filter (fun c : NeuralCode N => wt c = w)).card = N.choose w := by
  classical
  have hpc : ((Finset.univ : Finset (Fin N)).powersetCard w).card = N.choose w := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hpc]
  apply Finset.card_bij (fun c _ => supp c)
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    exact mem_powersetCard.mpr ⟨Finset.subset_univ _, hc⟩
  · intro a _ b _ hab
    funext i
    have hiff : (i ∈ supp a) ↔ (i ∈ supp b) := by rw [hab]
    simp only [supp, mem_filter, mem_univ, true_and] at hiff
    cases hai : a i <;> cases hbi : b i <;> simp_all
  · intro T hT
    simp only [mem_powersetCard] at hT
    refine ⟨fun i => decide (i ∈ T), ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and, wt]
      have : supp (fun i => decide (i ∈ T)) = T := by ext i; simp [supp]
      rw [this]; exact hT.2
    · ext i; simp [supp]
