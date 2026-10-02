-- Prove2me | solution 1 for BookSixth.composition_preserves_roundness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T00:26:02.74684+00:00
-- url     : https://prove2.me/submissions/4c0ddff4-1cca-47cb-88c6-93c16b25d99e

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- The gluing principle for round circles: the image of `C` under a composite of two maps
is the image of `C` under the second map, then under the first. `Set.image_comp` states
exactly that, so roundness of the intermediate image is roundness of the composed image. -/
theorem solution {α : Type*} (f g : Space3 → Space3) (C : Set Space3)
    (hf : RoundCircle (f '' (g '' C))) :
    RoundCircle ((fun x : Space3 => f (g x)) '' C) := by
  have hEq : (fun x : Space3 => f (g x)) '' C = f '' (g '' C) := by
    show (f ∘ g) '' C = f '' (g '' C)
    exact Set.image_comp f g C
  rw [hEq]
  exact hf
