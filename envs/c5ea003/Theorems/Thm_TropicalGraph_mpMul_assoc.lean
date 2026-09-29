-- Prove2me | Theorems.Thm_TropicalGraph_mpMul_assoc
-- name    : TropicalGraph.mpMul_assoc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:34:48.757989+00:00
-- url     : https://prove2.me/theorems/4add5fef-edc9-44fa-ad24-ed395dedfafb
-- title:
--   Associativity (Bellman's optimality principle).
-- statement:
--   **Associativity (Bellman's optimality principle).**  Splitting an optimal walk
--   at any point gives optimal sub-walks.
--
--   ```lean
--   theorem TropicalGraph.mpMul_assoc(A B C : Weighting n) : mpMul (mpMul A B) C = mpMul A (mpMul B C) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/TropicalspectralgraphTheorems/TropicalSpectralGraph_Theorems.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/TropicalspectralgraphTheorems/TropicalSpectralGraph_Theorems.lean#L57

-- Thm stub generated from Combinatorics/TropicalspectralgraphTheorems/TropicalSpectralGraph_Theorems.lean
import Mathlib
import Definitions.Def_Combinatorics_TropicalentropyDefs_TropicalEntropy_Defs
import Definitions.Def_Combinatorics_TropicalspectralgraphTheorems_TropicalSpectralGraph_Theorems

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

open TropicalGraph

open Finset TropicalEntropy

variable {n : ℕ} [NeZero n]

theorem TropicalGraph.mpMul_assoc(A B C : Weighting n) : mpMul (mpMul A B) C = mpMul A (mpMul B C) := by sorry
