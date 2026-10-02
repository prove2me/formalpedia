-- Prove2me | solution 1 for BookSixth.roundness_compose_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:01:44.770558+00:00
-- url     : https://prove2.me/submissions/f53dfafb-cc19-4f7b-9d94-7f6a3b14c556

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_roundness_of_similarity_isotopy

open scoped BigOperators
open BookSixth

/-- Composing a roundness-preserving motion with a similarity motion preserves roundness
at every time. The image identity is `Set.image_comp`, stated through an explicit `show`
so that the lambda/composition shape is checked rather than silently skipped. -/
theorem solution {C : Set Space3} (G : ℝ → Space3 ≃ₜ Space3)
    (hGsim : ∀ t, ∃ q : ℝ × Space3, 0 < q.1 ∧
        (∀ x : Space3, (G t) x = (q.1 • x) + q.2))
    (L : ℝ → Space3 ≃ₜ Space3)
    (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by
  intro t
  have hcomp : (fun s : Space3 => G t (L t s)) '' C = (G t) '' ((L t) '' C) := by
    show (G t ∘ L t) '' C = (G t) '' (L t) '' C
    exact Set.image_comp (G t) (L t) C
  rw [hcomp]
  exact BookSixth.roundness_of_similarity_isotopy (hLround t) G hGsim t
