-- Prove2me | solution 1 for BookSixth.roundness_compose_on_intermediate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-25T18:57:31.274986+00:00
-- url     : https://prove2.me/submissions/d5e43d85-417c-46bc-931b-4f946919cb36

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- Roundness of the composed image follows from roundness of the intermediate image.

The image of `C` under `G t ∘ L t` is exactly the image of the intermediate set
`(L t) '' C` under `G t`, so this is the set-theoretic identity underlying any gluing of
roundness-preserving motions. -/
theorem solution {C : Set Space3}
    (G : ℝ → Space3 ≃ₜ Space3) (L : ℝ → Space3 ≃ₜ Space3)
    (hGround : ∀ t, RoundCircle ((G t) '' ((L t) '' C))) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by
  intro t
  have hcomp : (fun s : Space3 => G t (L t s)) '' C = (G t) '' ((L t) '' C) := by
    show (G t ∘ L t) '' C = (G t) '' (L t) '' C
    exact Set.image_comp (G t) (L t) C
  rw [hcomp]
  exact hGround t
