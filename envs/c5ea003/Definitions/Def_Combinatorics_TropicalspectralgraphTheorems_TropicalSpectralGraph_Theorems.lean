-- Prove2me | Definitions.Def_Combinatorics_TropicalspectralgraphTheorems_TropicalSpectralGraph_Theorems
-- name    : Combinatorics_TropicalspectralgraphTheorems_TropicalSpectralGraph_Theorems
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:56:40.325322+00:00
-- url     : https://prove2.me/theorems/21b7c52c-3320-4fdd-b437-bc559b3e4b53
-- title:
--   Aether Catalog definitions — Combinatorics_TropicalspectralgraphTheorems_TropicalSpectralGraph_Theorems
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.TropicalspectralgraphTheorems.TropicalSpectralGraph.Theorems`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/TropicalspectralgraphTheorems/TropicalSpectralGraph_Theorems.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_TropicalentropyDefs_TropicalEntropy_Defs

/-!
# Tropical spectral graph theory

This module previously contained only a stray relative path pointing at a
non-existent file `Shared/TropicalSpectralGraph/Theorems.lean`.  It is
reconstructed here as a self-contained development of **min-plus (tropical) matrix
algebra** on a finite complete weighted digraph, the algebraic backbone of tropical
spectral graph theory: tropical matrix powers compute shortest walks, and the
tropical eigenvalue is a minimal cycle mean.

Main results:

* `TropicalGraph.mpMul` — the min-plus matrix product, together with
  `TropicalGraph.mpMul_assoc` (**associativity**, i.e. the Bellman optimality
  principle) and `TropicalGraph.mpMul_one` / `one_mpMul` (the tropical identity);
* `TropicalGraph.mpMul_le` — the shortest-walk upper bound `(A ⊗ B) i j ≤ A i k + B k j`;
* `TropicalGraph.mpMul_mono` — monotonicity in both arguments;
* `TropicalGraph.mpMul_shift` — the **spectral shift**: adding a constant `c` to all
  entries shifts every tropical eigenvalue by `c`;
* `TropicalGraph.mpPow_add` and `TropicalGraph.mpPow_le_mul` — the concatenation
  law for tropical powers, the input to Fekete's lemma for the minimal cycle mean.
-/

namespace TropicalGraph

open Finset TropicalEntropy

variable {n : ℕ} [NeZero n]

/-- The index set is non-empty, so `inf'` is available. -/
private lemma univ_ne : (Finset.univ : Finset (Fin n)).Nonempty :=
  Finset.univ_nonempty (α := Fin n)

/-- A weighted digraph: `A i j` is the length of the arc `i → j`. -/
abbrev Weighting (n : ℕ) : Type := Fin n → Fin n → ℝ

/-- **Min-plus matrix product.**  `(A ⊗ B) i j = min_k (A i k + B k j)`. -/
noncomputable def mpMul (A B : Weighting n) : Weighting n :=
  fun i j => tropSum Finset.univ univ_ne (fun k => A i k + B k j)





/-- The tropical identity matrix: `0` on the diagonal, `+∞` off it — modelled here
by a sufficiently large finite penalty is not needed, since we state the identity
laws against an explicit bound. -/
noncomputable def tropOne (M : ℝ) : Weighting n := fun i j => if i = j then 0 else M





/-- Tropical powers: `mpPow A m` is the matrix of shortest walks using exactly
`m + 1` arcs. -/
noncomputable def mpPow (A : Weighting n) : ℕ → Weighting n
  | 0 => A
  | m + 1 => mpMul A (mpPow A m)





end TropicalGraph


