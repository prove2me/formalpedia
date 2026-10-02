-- Prove2me | solution 1 for BookSixth.roundness_of_rigid_translate_compose
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:31:58.633994+00:00
-- url     : https://prove2.me/submissions/aa7e8a49-f8dd-424e-a869-90ee1045a509

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_roundness_of_rigid_isotopy

open scoped BigOperators
open BookSixth

/-- Two rigid motions in sequence keep every image round. The image identity is
`Set.image_comp`, stated through an explicit `show` so that the lambda/composition
shape is checked rather than silently skipped. -/
theorem solution {C : Set Space3} (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ q : ℝ × Space3,
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = (A x) + q.2))
    (L : ℝ → Space3 ≃ₜ Space3)
    (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by
  intro t
  have hcomp : (fun s : Space3 => G t (L t s)) '' C = (G t) '' ((L t) '' C) := by
    show (G t ∘ L t) '' C = (G t) '' (L t) '' C
    exact Set.image_comp (G t) (L t) C
  rw [hcomp]
  exact BookSixth.roundness_of_rigid_isotopy (hLround t) G hG t
