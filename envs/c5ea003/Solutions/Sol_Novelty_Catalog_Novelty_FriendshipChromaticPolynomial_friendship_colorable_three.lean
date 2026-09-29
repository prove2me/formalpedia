-- Prove2me | solution 1 for Novelty.Catalog.Novelty.FriendshipChromaticPolynomial.friendship_colorable_three
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:44:55.161972+00:00
-- url     : https://prove2.me/submissions/fe18660c-0e44-41cc-b8b8-04cc7108cdd6

import Mathlib
import Definitions.Def_Novelty_FriendshipChromaticPolynomial
open Catalog.Novelty.FriendshipChromaticPolynomial in
theorem solution (n : ℕ) : (friendship n).Colorable 3 := by
  -- the hub gets colour 0; each blade's two ends get colours 1 and 2
  let c : Option (Fin n × Bool) → Fin 3 := fun v =>
    match v with
    | none => 0
    | some (_, false) => 1
    | some (_, true) => 2
  refine ⟨SimpleGraph.Coloring.mk c ?_⟩
  intro v w hvw
  rcases v with _ | ⟨i, _ | _⟩ <;> rcases w with _ | ⟨j, _ | _⟩ <;>
    simp_all [friendship, frAdj, c]
