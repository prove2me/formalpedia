-- Prove2me | solution 1 for Kourovka.retract_eq_bot_of_le_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:48.413284+00:00
-- url     : https://prove2.me/submissions/004e7fb9-504a-4686-98b6-0642bff88cda

import Definitions.Def_Kourovka_Components
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.QuotientGroup.Basic
import Definitions.Def_Kourovka_CentralProducts
import Theorems.Thm_Kourovka_subsingleton_of_solvable_perfect


set_option autoImplicit true
open Kourovka
variable {G : Type*} [Group G]
namespace Kourovka
theorem _root_.solution [IsSolvable G] (T : Subgroup G)
    (r : G →* T) (hr : ∀ t : T, r t = t) (hT : T ≤ commutator G) : T = ⊥ := by
  have hsurj : Function.Surjective r := fun t => ⟨t, hr t⟩
  have hmap : (commutator G).map r = commutator T := by
    rw [map_commutator_eq, (MonoidHom.range_eq_top.mpr hsurj), commutator_def]
  have hperfect : commutator T = ⊤ := by
    apply top_unique
    intro t _
    rw [← hmap]
    exact ⟨t, hT t.property, hr t⟩
  letI : Subsingleton T := subsingleton_of_solvable_perfect hperfect
  exact T.eq_bot_of_subsingleton
end Kourovka
