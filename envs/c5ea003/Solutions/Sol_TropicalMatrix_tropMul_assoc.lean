-- Prove2me | solution 1 for TropicalMatrix.tropMul_assoc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:56:38.663948+00:00
-- url     : https://prove2.me/submissions/cfa03d32-2835-4758-9170-56ae8bb52c1d

-- Sol generated from Tropical/TropicalAlgebra/MinPlusSpectral.lean
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


open TropicalMatrix in
theorem solution[Nonempty (Fin n)]
    (A B C : Matrix (Fin n) (Fin n) ℝ) :
    tropMul (tropMul A B) C = tropMul A (tropMul B C) := by
  ext i j;
  nontriviality;
  refine' le_antisymm _ _ <;> simp +decide [ tropMul ];
  · intro k;
    -- By definition of infimum, there exists some $l$ such that $B k l + C l j \leq \inf_{l} (B k l + C l j)$.
    obtain ⟨l, hl⟩ : ∃ l, B k l + C l j ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun l => B k l + C l j) := by
      exact Finset.exists_min_image Finset.univ ( fun l => B k l + C l j ) ⟨ k, Finset.mem_univ k ⟩ |> fun ⟨ l, hl₁, hl₂ ⟩ => ⟨ l, Finset.le_inf' _ _ fun x hx => hl₂ x hx ⟩;
    exact ⟨ l, by linarith [ show A i k + B k l ≥ Finset.inf' Finset.univ Finset.univ_nonempty ( fun k_1 => A i k_1 + B k_1 l ) from Finset.inf'_le _ ( Finset.mem_univ k ) ] ⟩;
  · intro b;
    obtain ⟨ k, hk ⟩ := Finset.exists_min_image Finset.univ ( fun k => A i k + B k b ) ⟨ b, Finset.mem_univ b ⟩;
    use k;
    obtain ⟨ l, hl ⟩ := Finset.exists_min_image Finset.univ ( fun k_1 => B k k_1 + C k_1 j ) ⟨ b, Finset.mem_univ b ⟩ ; simp_all +decide [ Finset.inf'_le_iff ];
    rw [ show ( Finset.univ.inf' Finset.univ_nonempty fun k_1 => B k k_1 + C k_1 j ) = B k l + C l j from le_antisymm ( Finset.inf'_le _ <| Finset.mem_univ _ ) <| Finset.le_inf' _ _ fun x hx => hl x ] ; linarith [ hk b, hl b, show ( Finset.univ.inf' Finset.univ_nonempty fun k => A i k + B k b ) ≥ A i k + B k b from Finset.le_inf' _ _ fun x hx => hk x ]
