-- Prove2me | solution 1 for NeuralSparseCode.sparse_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:03:31.423987+00:00
-- url     : https://prove2.me/submissions/a3115846-b44f-426e-9218-7df3fb7cae0e

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
theorem solution{N w s : ℕ} (C : Finset (NeuralCode N))
    (hw : ∀ c ∈ C, wt c = w)
    (hint : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (supp x ∩ supp y).card < s) :
    C.card * w.choose s ≤ N.choose s := by
  classical
  have hdisj : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      Disjoint ((supp x).powersetCard s) ((supp y).powersetCard s) := by
    intro x hx y hy hxy
    simp only [Finset.disjoint_left, mem_powersetCard]
    rintro T ⟨hTx, hTs⟩ ⟨hTy, -⟩
    have hTsub : T ⊆ supp x ∩ supp y := Finset.subset_inter hTx hTy
    have h1 := Finset.card_le_card hTsub
    have h2 := hint x hx y hy hxy
    omega
  have hcard : (C.biUnion (fun c => (supp c).powersetCard s)).card
      = ∑ c ∈ C, ((supp c).powersetCard s).card :=
    Finset.card_biUnion (fun x hx y hy hxy => hdisj x hx y hy hxy)
  have hsub : C.biUnion (fun c => (supp c).powersetCard s)
      ⊆ (Finset.univ : Finset (Fin N)).powersetCard s := by
    intro T hT
    simp only [mem_biUnion, mem_powersetCard] at hT ⊢
    obtain ⟨c, -, -, hTs⟩ := hT
    exact ⟨Finset.subset_univ _, hTs⟩
  have hle := Finset.card_le_card hsub
  rw [hcard, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at hle
  have hterm : ∀ c ∈ C, ((supp c).powersetCard s).card = w.choose s := by
    intro c hc
    rw [Finset.card_powersetCard, ← wt, hw c hc]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul] at hle
  exact hle
