-- Prove2me | Definitions.Def_Novelty_NeuralCodeSparsePacking
-- name    : Novelty_NeuralCodeSparsePacking
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:35.095093+00:00
-- url     : https://prove2.me/theorems/1a3ab709-2479-4a4c-b6de-becc86e53c57
-- title:
--   Aether Catalog definitions — Novelty_NeuralCodeSparsePacking
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NeuralCodeSparsePacking`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NeuralCodeSparsePacking.lean by skeleton subtraction
import Mathlib

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

namespace NeuralSparseCode

open Finset

/-- A **neural code** on `N` neurons. -/
abbrev NeuralCode (N : ℕ) : Type := Fin N → Bool

/-- The **assembly** (support) of a pattern: the set of active neurons. -/
def supp {N : ℕ} (c : NeuralCode N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => c i = true)

/-- The **weight** (sparseness level) of a pattern: the size of its assembly. -/
def wt {N : ℕ} (c : NeuralCode N) : ℕ := (supp c).card






/-! ## Tightness -/

/-- The **grandmother cell** for neuron `i`: only neuron `i` fires. -/
def oneHot {N : ℕ} (i : Fin N) : NeuralCode N := fun j => decide (j = i)




/-! ## The full sparse layer -/



end NeuralSparseCode


