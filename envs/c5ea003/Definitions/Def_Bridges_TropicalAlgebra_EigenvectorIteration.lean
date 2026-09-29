-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_EigenvectorIteration
-- name    : Bridges_TropicalAlgebra_EigenvectorIteration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:40.354989+00:00
-- url     : https://prove2.me/theorems/d0b23deb-7727-46c5-9b36-1354a1451528
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_EigenvectorIteration
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.EigenvectorIteration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/EigenvectorIteration.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_MaxPlusDefs

/-!
# Eigenvector Iteration and Spectral Growth

Given a tropical eigenvector `v` with eigenvalue `μ`, we prove:
1. Adding a constant commutes with max-plus multiplication
2. Iterating `maxPlusMul M` k times on an eigenvector yields `k·μ + v`
3. The bounded defect growth theorem follows

## Key insight

Instead of using `tropicalMatPow` (which requires a tropical identity that doesn't
exist over `ℝ`), we work with iterated application of `maxPlusMul M`. This avoids
the `-∞` issue entirely and gives cleaner statements.
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}

/-! ### Iterated max-plus multiplication -/

/-- Iterated application of max-plus matrix-vector multiplication. -/
def iterMaxPlusMul (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ℕ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, v => v
  | k + 1, v => maxPlusMul M (iterMaxPlusMul hn M k v) hn



/-! ### Shift lemma -/

/-
Max-plus multiplication commutes with adding a constant to the vector:
    `M ⊗ (c + v) = c + (M ⊗ v)`.
-/

/-! ### The iteration theorem -/

/-
**Eigenvector iteration theorem**: If `v` is an eigenvector with eigenvalue `μ`,
    then the k-th iterate of `maxPlusMul M` applied to `v` yields `k·μ + v`.

    This is the fundamental bridge from eigenvectors to asymptotic growth.
-/

/-! ### Bounds from iterates -/


/-! ### Bounded defect growth from eigenvector -/

/-
If `M` admits an eigenvector with eigenvalue `μ`, then the max entry of
    the k-th iterate applied to the eigenvector grows as `k·μ + maxᵢ vᵢ`.
-/

end


