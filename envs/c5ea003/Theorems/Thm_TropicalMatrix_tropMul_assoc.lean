-- Prove2me | Theorems.Thm_TropicalMatrix_tropMul_assoc
-- name    : TropicalMatrix.tropMul_assoc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:40:16.428614+00:00
-- url     : https://prove2.me/theorems/30543ade-c0a1-49a4-8e52-bd3b78858870
-- title:
--   TropMul assoc
-- statement:
--   Formal statement of `TropicalMatrix.tropMul_assoc` from the Aether Catalog (Tropical). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalMatrix.tropMul_assoc[Nonempty (Fin n)]
--       (A B C : Matrix (Fin n) (Fin n) ℝ) :
--       tropMul (tropMul A B) C = tropMul A (tropMul B C) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalAlgebra/MinPlusSpectral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalAlgebra/MinPlusSpectral.lean#L63

-- Thm stub generated from Tropical/TropicalAlgebra/MinPlusSpectral.lean
import Mathlib
import Definitions.Def_Tropical_TropicalAlgebra_MinPlusSpectral
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical (Min-Plus) Matrix Algebra and Spectral Theory

This file defines min-plus matrix multiplication and proves that diagonal entries
of tropical powers satisfy a subadditive inequality. This is the formal kernel of
tropical spectral theory: it implies the existence of asymptotic cycle means
(tropical eigenvalues) via Fekete's lemma.

## Main results

- `tropMul`: Min-plus matrix multiplication
- `tropPow`: Iterated min-plus matrix power
- `tropMul_diag_le`: Diagonal entry of product bounded by sum of diagonal entries
- `tropMul_assoc`: Associativity of tropical multiplication
- `tropPow_succ`: Unfolding of tropical power
- `tropPow_add`: Key composition law: `tropPow A (m + k) = tropMul (tropPow A m) (tropPow A k)`
- `tropPow_diag_subadditive`: **Flagship theorem** — diagonal entries of tropical
  powers are subadditive: `(A^⊗(m+k))_{ii} ≤ (A^⊗m)_{ii} + (A^⊗k)_{ii}`

## Mathematical significance

Subadditivity of the diagonal sequence `a_n = (A^{⊗n})_{ii}` implies by Fekete's
lemma that `lim a_n/n` exists, yielding the tropical eigenvalue (minimum cycle mean).
This is the foundation for Karp's theorem, tropical Perron-Frobenius theory,
and shortest-path asymptotics.
-/

open Finset BigOperators

open TropicalMatrix

variable {n : ℕ}


/-
The diagonal entry of a tropical product is at most the sum of diagonal entries.
    This uses the witness `k = i` in the infimum.
-/

/-
Tropical multiplication is bounded below by any pair of entries.
-/

/-
Associativity of tropical multiplication.
-/

theorem TropicalMatrix.tropMul_assoc[Nonempty (Fin n)]
    (A B C : Matrix (Fin n) (Fin n) ℝ) :
    tropMul (tropMul A B) C = tropMul A (tropMul B C) := by sorry
