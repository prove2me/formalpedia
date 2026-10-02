-- Prove2me | solution 1 for BookSixth.roundness_of_scaled_orthogonal_compose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:52:11.344986+00:00
-- url     : https://prove2.me/submissions/6156af40-bab9-4ade-a0e1-6e79886f0f41

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_roundness_of_rigid_similarity_isotopy

open scoped BigOperators
open BookSixth

/-- Composing a roundness-preserving motion with a scaled orthogonal motion preserves
roundness at every time. The image identity is `Set.image_comp`, stated through an
explicit `show` so that the lambda/composition shape is checked rather than silently
skipped. -/
theorem solution {C : Set Space3} (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : Space3, 0 < a ∧
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = a • (A x) + b))
    (L : ℝ → Space3 ≃ₜ Space3)
    (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by
  intro t
  have hcomp : (fun s : Space3 => G t (L t s)) '' C = (G t) '' ((L t) '' C) := by
    show (G t ∘ L t) '' C = (G t) '' (L t) '' C
    exact Set.image_comp (G t) (L t) C
  rw [hcomp]
  exact BookSixth.roundness_of_rigid_similarity_isotopy (hLround t) G hG t
