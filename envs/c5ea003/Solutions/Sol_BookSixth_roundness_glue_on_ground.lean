-- Prove2me | solution 1 for BookSixth.roundness_glue_on_ground
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T00:33:02.079018+00:00
-- url     : https://prove2.me/submissions/d8272bd0-c6f1-4a50-9339-f74dcaa9255c

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- Gluing a roundness-preserving motion onto a roundness-preserving prefix. At each time
the image of `C` under the composite is, by `Set.image_comp`, the image of the
intermediate round circle `(L t) '' C` under `G t`, and the hypothesis on `G` says that is
round. -/
theorem solution {C : Set Space3} (G : ℝ → Space3 ≃ₜ Space3)
    (hGround : ∀ (D : Set Space3), ∀ t, RoundCircle D → RoundCircle ((G t) '' D))
    (L : ℝ → Space3 ≃ₜ Space3) (hLround : ∀ t, RoundCircle ((L t) '' C)) :
    ∀ t, RoundCircle ((fun s => G t (L t s)) '' C) := by
  intro t
  have hcomp : (fun s : Space3 => G t (L t s)) '' C = (G t) '' ((L t) '' C) := by
    show (G t ∘ L t) '' C = (G t) '' (L t) '' C
    exact Set.image_comp (G t) (L t) C
  rw [hcomp]
  exact hGround ((L t) '' C) t (hLround t)
