-- Prove2me | solution 1 for RHLinalg.bilinear_doublyStochastic_le_of_monovary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:52:26.153614+00:00
-- url     : https://prove2.me/submissions/0b5df495-f02c-49f8-90a3-9205de9b1ba2

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_VonNeumann

-- from Zeta23.LinAlg.VonNeumann
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Von Neumann's trace inequality

For Hermitian `A, B` with eigenvalues sorted in decreasing order
`a₀ ≥ a₁ ≥ …` and `b₀ ≥ b₁ ≥ …`,

  `Re tr(AB) ≤ ∑ᵢ aᵢ bᵢ`.

## Proof outline

Diagonalise `A = Uₐ Dₐ Uₐᴴ` and `B = Uᵦ Dᵦ Uᵦᴴ`. Setting `W := Uₐᴴ Uᵦ`
(unitary), a direct calculation gives

  `tr(AB) = tr(Dₐ W Dᵦ Wᴴ) = ∑ₖₗ aₖ · ‖Wₖₗ‖² · bₗ`.

The matrix `Sₖₗ := ‖Wₖₗ‖²` is doubly stochastic over `ℝ` (rows and columns
of a unitary matrix are unit vectors). By **Birkhoff–von Neumann**
(`exists_eq_sum_perm_of_mem_doublyStochastic`) every doubly stochastic
matrix is a convex combination of permutation matrices: `S = ∑_σ w_σ P_σ`.
For each permutation `σ`, `∑ₖ aₖ b_{σ k} ≤ ∑ₖ aₖ bₖ` by the **rearrangement
inequality** (`Monovary.sum_mul_comp_perm_le_sum_mul`), since both `a` and
`b` are antitone (hence monovary). Averaging over `σ` with weights `w_σ`
gives the result.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]


section Bilinear



end Bilinear

section Rearrangement



end Rearrangement


end RHLinalg
end
open Matrix Finset
open scoped ComplexOrder
open RHLinalg
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution {a b : n → ℝ}
    (hab : Monovary a b) {S : Matrix n n ℝ} (hS : S ∈ doublyStochastic ℝ n) :
    ∑ k, ∑ l, a k * S k l * b l ≤ ∑ k, a k * b k := by
  -- LHS `= ∑ₖ aₖ · (S *ᵥ b)ₖ`.
  have hlhs : ∑ k, ∑ l, a k * S k l * b l = ∑ k, a k * (S *ᵥ b) k := by
    simp only [mulVec, dotProduct, mul_sum, mul_assoc]
  rw [hlhs]
  -- Birkhoff: `S = ∑_σ w_σ • P_σ`.
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic hS
  rw [← hw_eq]
  simp only [sum_mulVec, smul_mulVec, permMatrix_mulVec, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Function.comp_apply, mul_sum]
  rw [sum_comm]
  -- `∑_σ ∑ₖ aₖ · (w_σ · b(σ k)) = ∑_σ w_σ · ∑ₖ aₖ · b(σ k) ≤ ∑ₖ aₖ bₖ`.
  calc ∑ σ : Equiv.Perm n, ∑ k, a k * (w σ * b (σ k))
      = ∑ σ, w σ * ∑ k, a k * b (σ k) := by
        refine sum_congr rfl fun σ _ => ?_
        rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
    _ ≤ ∑ σ, w σ * ∑ k, a k * b k := by
        refine sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (hw_nonneg σ)
        exact hab.sum_mul_comp_perm_le_sum_mul (σ := σ)
    _ = ∑ k, a k * b k := by rw [← sum_mul, hw_sum, one_mul]
