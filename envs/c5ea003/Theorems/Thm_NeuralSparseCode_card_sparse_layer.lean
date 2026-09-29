-- Prove2me | Theorems.Thm_NeuralSparseCode_card_sparse_layer
-- name    : NeuralSparseCode.card_sparse_layer
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:12:29.084504+00:00
-- url     : https://prove2.me/theorems/02710ced-a7c6-4fb1-8868-8f8bf79c0ab1
-- title:
--   Sparse counts.
-- statement:
--   **Sparse counts.**  Exactly `C(N,w)` patterns have weight `w`.
--
--   ```lean
--   theorem NeuralSparseCode.card_sparse_layer(N w : ℕ) :
--       (Finset.univ.filter (fun c : NeuralCode N => wt c = w)).card = N.choose w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/NeuralCodeSparsePacking.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/NeuralCodeSparsePacking.lean#L175

-- Thm stub generated from Novelty/NeuralCodeSparsePacking.lean
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

theorem NeuralSparseCode.card_sparse_layer(N w : ℕ) :
    (Finset.univ.filter (fun c : NeuralCode N => wt c = w)).card = N.choose w := by sorry
