-- Prove2me | solution 1 for ToricCode.rank_d2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:45:16.154583+00:00
-- url     : https://prove2.me/submissions/dbc40bab-4f88-4d43-9ce9-effd9955a7c9

-- Sol generated from Geometry/ToricCode/Homology.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_card_face
import Theorems.Thm_ToricCode_ker_d2
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


lemma finrank_ker_d2 : Module.finrank F2 (LinearMap.ker (d2 M N).mulVecLin) = 1 := by
  rw [ker_d2]
  exact finrank_const_line








open ToricCode in
theorem solution: (d2 M N).rank = M * N - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (d2 M N).mulVecLin
  rw [finrank_ker_d2, Module.finrank_fintype_fun_eq_card, card_face M N] at h
  show Module.finrank F2 (LinearMap.range (d2 M N).mulVecLin) = M * N - 1
  omega
