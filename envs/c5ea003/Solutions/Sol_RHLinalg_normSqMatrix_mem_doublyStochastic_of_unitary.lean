-- Prove2me | solution 1 for RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:49:29.429129+00:00
-- url     : https://prove2.me/submissions/b8f1abeb-82c2-487b-81df-fa7204499de7

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

theorem solution
    {W : Matrix n n 𝕜} (hW : W ∈ Matrix.unitaryGroup n 𝕜) :
    normSqMatrix W ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · -- row sum: `∑ⱼ ‖Wᵢⱼ‖² = re (W Wᴴ)ᵢᵢ = re 1 = 1`
    have h : (W * star W) i i = 1 := by rw [Unitary.mul_star_self_of_mem hW]; simp
    have h2 : RCLike.re ((W * star W) i i) = (1 : ℝ) := by rw [h]; simp
    simpa [normSqMatrix, Matrix.mul_apply, star_apply, RCLike.star_def,
      RCLike.mul_conj, map_sum] using h2
  · -- column sum: `∑ᵢ ‖Wᵢⱼ‖² = re (Wᴴ W)ⱼⱼ = re 1 = 1`
    have h : (star W * W) j j = 1 := by rw [Unitary.star_mul_self_of_mem hW]; simp
    have h2 : RCLike.re ((star W * W) j j) = (1 : ℝ) := by rw [h]; simp
    simpa [normSqMatrix, Matrix.mul_apply, star_apply, RCLike.star_def,
      RCLike.conj_mul, map_sum] using h2
