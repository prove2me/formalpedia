-- Prove2me | solution 1 for ToricCode.ker_d2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:43:40.185438+00:00
-- url     : https://prove2.me/submissions/035a061e-f98f-4d11-933d-13586a5aa5c7

-- Sol generated from Geometry/ToricCode/Homology.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_const_of_shift
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











open ToricCode in
theorem solution:
    LinearMap.ker (d2 M N).mulVecLin = F2 ∙ (fun _ => 1 : Face M N → F2) := by
  apply le_antisymm
  · intro g hg
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hg
    have key : ∀ (b : Bool) (u : ZMod M × ZMod N), g u + g (u - step M N (!b)) = 0 := by
      intro b u
      rw [← d2_mulVec M N g b u, hg]
      rfl
    have h2 : ∀ x y : F2, x + y = 0 → y = x := by decide
    have hx : ∀ u : ZMod M × ZMod N, g (u + (1, 0)) = g u := by
      intro u
      have := key true (u + (1, 0))
      simp only [Bool.not_true, step_false, add_sub_cancel_right] at this
      exact (h2 _ _ this).symm
    have hy : ∀ u : ZMod M × ZMod N, g (u + (0, 1)) = g u := by
      intro u
      have := key false (u + (0, 1))
      simp only [Bool.not_false, step_true, add_sub_cancel_right] at this
      exact (h2 _ _ this).symm
    rw [Submodule.mem_span_singleton]
    refine ⟨g 0, ?_⟩
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    exact (const_of_shift M N g hx hy u).symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    funext e
    obtain ⟨b, u⟩ := e
    rw [d2_mulVec]
    show (1 : F2) + 1 = 0
    decide
