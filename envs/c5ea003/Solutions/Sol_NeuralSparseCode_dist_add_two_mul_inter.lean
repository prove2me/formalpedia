-- Prove2me | solution 1 for NeuralSparseCode.dist_add_two_mul_inter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:03:29.780413+00:00
-- url     : https://prove2.me/submissions/05bb07de-1c4b-4ea1-95c5-111e80fc1543

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
theorem solution{N : ℕ} (x y : NeuralCode N) :
    hammingDist x y + 2 * (supp x ∩ supp y).card = wt x + wt y := by
  have hfil : (Finset.univ.filter (fun i => x i ≠ y i))
      = (supp x \ supp y) ∪ (supp y \ supp x) := by
    ext i
    simp only [supp, mem_filter, mem_univ, true_and, mem_union, mem_sdiff]
    cases hx : x i <;> cases hy : y i <;> simp
  have hdisj : Disjoint (supp x \ supp y) (supp y \ supp x) := by
    simp only [Finset.disjoint_left, mem_sdiff]
    rintro a ⟨-, h2⟩ ⟨h3, -⟩
    exact h2 h3
  have hd : hammingDist x y = (supp x \ supp y).card + (supp y \ supp x).card := by
    rw [hammingDist, hfil, Finset.card_union_of_disjoint hdisj]
  have h1 : (supp x \ supp y).card + (supp x ∩ supp y).card = wt x :=
    Finset.card_sdiff_add_card_inter _ _
  have h2 : (supp y \ supp x).card + (supp y ∩ supp x).card = wt y :=
    Finset.card_sdiff_add_card_inter _ _
  rw [Finset.inter_comm (supp y) (supp x)] at h2
  omega
