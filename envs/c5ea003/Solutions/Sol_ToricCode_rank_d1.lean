-- Prove2me | solution 1 for ToricCode.rank_d1
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:47:57.368318+00:00
-- url     : https://prove2.me/submissions/acba7143-16b3-4261-931d-669ab08b5eb7

-- Sol generated from Geometry/ToricCode/Homology.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_card_vert
import Theorems.Thm_ToricCode_ker_d1T
/-!
# First homology of the square torus: rank exactly two

We compute `dim_{𝔽₂} H₁ = dim ker d₁ - dim im d₂ = 2` for the `M × N` square
torus, for *every* `M, N ≥ 1`.

The computation avoids any explicit basis of the cycle space.  Instead:

* the kernel of the coboundary `d₁ᵀ` is the line of constant `0`-cochains
  (`ker_d1T`), because the vertex graph of the torus is connected;
* the kernel of `d₂` is the line of constant `2`-chains (`ker_d2`), because the
  dual graph is connected;
* hence `rank d₁ᵀ = MN - 1`, and `rank d₁ = rank d₁ᵀ` by the row-rank/column-rank
  theorem, so `dim ker d₁ = 2MN - (MN - 1) = MN + 1`;
* and `dim im d₂ = MN - 1`;
* subtracting gives `2`.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]





/-! ### The two connectivity lemmas -/



/-! ### Rank computations -/

private lemma finrank_const_line {α : Type*} [Fintype α] [Nonempty α] :
    Module.finrank F2 (F2 ∙ (fun _ => 1 : α → F2)) = 1 := by
  apply finrank_span_singleton
  intro h
  have := congrFun h (Classical.arbitrary α)
  simp at this

lemma finrank_ker_d1T : Module.finrank F2 (LinearMap.ker ((d1 M N)ᵀ).mulVecLin) = 1 := by
  rw [ker_d1T]
  exact finrank_const_line









open ToricCode in
theorem solution: (d1 M N).rank = M * N - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((d1 M N)ᵀ).mulVecLin
  rw [finrank_ker_d1T, Module.finrank_fintype_fun_eq_card, card_vert M N] at h
  have : ((d1 M N)ᵀ).rank = M * N - 1 := by
    show Module.finrank F2 (LinearMap.range ((d1 M N)ᵀ).mulVecLin) = M * N - 1
    omega
  rwa [Matrix.rank_transpose] at this
