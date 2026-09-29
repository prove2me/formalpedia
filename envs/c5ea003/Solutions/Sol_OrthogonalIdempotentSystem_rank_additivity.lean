-- Prove2me | solution 1 for OrthogonalIdempotentSystem.rank_additivity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T19:00:29.074959+00:00
-- url     : https://prove2.me/submissions/02343e14-3e0e-4894-9ef9-9dc63a8bbf02

import Mathlib
import Definitions.Def_Geometry_NeuralCoding_StandardConjectures
open Finset BigOperators LinearMap Module OrthogonalIdempotentSystem in
theorem solution {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ}
    (S : OrthogonalIdempotentSystem F V n) [FiniteDimensional F V] :
    finrank F V = ∑ i : Fin n, finrank F (S.gradedPiece i) := by
  -- on the image of `π i`, the projector `π j` acts as `δ_ij`
  have hact : ∀ (i j : Fin n) (y : V), y ∈ LinearMap.range (S.π i) →
      S.π j y = if j = i then y else 0 := by
    rintro i j _ ⟨w, rfl⟩
    split_ifs with h
    · subst h
      exact LinearMap.congr_fun (S.idem j) w
    · exact LinearMap.congr_fun (S.ortho j i h) w
  have hsum : ∀ v : V, ∑ i, S.π i v = v := by
    intro v
    have := LinearMap.congr_fun S.complete v
    rwa [LinearMap.sum_apply] at this
  -- `V` is the direct product of the graded pieces
  let e : V ≃ₗ[F] (∀ i, S.gradedPiece i) :=
    { toFun := fun v i => ⟨S.π i v, LinearMap.mem_range_self _ _⟩
      map_add' := fun v w => by
        funext i
        ext
        simp
      map_smul' := fun c v => by
        funext i
        ext
        simp
      invFun := fun x => ∑ i, (x i : V)
      left_inv := fun v => hsum v
      right_inv := fun x => by
        funext j
        ext
        simp only [map_sum]
        rw [sum_eq_single j]
        · rw [hact j j _ (x j).2, if_pos rfl]
        · intro i _ hij
          rw [hact i j _ (x i).2, if_neg (Ne.symm hij)]
        · intro h
          exact absurd (mem_univ j) h }
  rw [e.finrank_eq, Module.finrank_pi_fintype]
