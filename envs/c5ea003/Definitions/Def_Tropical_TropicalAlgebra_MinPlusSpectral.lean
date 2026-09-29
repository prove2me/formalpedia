-- Prove2me | Definitions.Def_Tropical_TropicalAlgebra_MinPlusSpectral
-- name    : Tropical_TropicalAlgebra_MinPlusSpectral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:03.609877+00:00
-- url     : https://prove2.me/theorems/dee1966b-e441-4ca9-8402-eb5e8077436e
-- title:
--   Aether Catalog definitions — Tropical_TropicalAlgebra_MinPlusSpectral
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalAlgebra.MinPlusSpectral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalAlgebra/MinPlusSpectral.lean by skeleton subtraction
import Mathlib
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

namespace TropicalMatrix

variable {n : ℕ}

/-- Min-plus (tropical) matrix multiplication:
    `(A ⊗ B)_{ij} = min_k (A_{ik} + B_{kj})` -/
noncomputable def tropMul [Nonempty (Fin n)] (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Finset.inf' Finset.univ Finset.univ_nonempty (fun k => A i k + B k j)

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

/-- Tropical power: A^{⊗0} is A itself (the "1-step" matrix),
    A^{⊗(n+1)} = tropMul (A^{⊗n}) A.
    Note: This is 0-indexed, so tropPow A 0 = A (1-step paths),
    tropPow A 1 = A ⊗ A (2-step paths), etc. -/
noncomputable def tropPow [Nonempty (Fin n)] :
    Matrix (Fin n) (Fin n) ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ
  | A, 0 => A
  | A, m + 1 => tropMul (tropPow A m) A

/-
Composition law for tropical powers:
    `tropPow A (m + k + 1) = tropMul (tropPow A m) (tropPow A k)`
-/

/-
**Flagship theorem**: Diagonal entries of tropical powers are subadditive.

    For any matrix `A` and index `i`:
    `(A^{⊗(m+k+1)})_{ii} ≤ (A^{⊗m})_{ii} + (A^{⊗k})_{ii}`

    This is the formal kernel of tropical spectral theory. By Fekete's lemma,
    it implies that the sequence `(A^{⊗n})_{ii} / n` converges, giving the
    tropical eigenvalue (minimum cycle mean through vertex i).
-/

end TropicalMatrix


