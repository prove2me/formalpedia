-- Prove2me | solution 1 for Kourovka.CenterQuotients.retract_trivial_of_killed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:09.574624+00:00
-- url     : https://prove2.me/submissions/9f558042-f86a-43a5-b028-9c36c85c0307

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_CenterQuotients
import Theorems.Thm_Kourovka_ker_le_commutator_of_surjective
import Theorems.Thm_Kourovka_subsingleton_of_solvable_perfect


set_option autoImplicit true
open Kourovka
open Kourovka.CenterQuotients
variable {A B G H T : Type*} [Group A] [Group B] [Group G] [Group H] [Group T]
namespace Kourovka.CenterQuotients
theorem _root_.solution [Group.FG G] [IsSolvable T]
    (f : G →* G) (hf : Function.Surjective f) (i : T →* G) (r : G →* T)
    (hri : ∀ t, r (i t) = t) (hkill : ∀ t, f (i t) = 1) : ∀ t : T, t = 1 := by
  have hr : Function.Surjective r := fun t => ⟨i t, hri t⟩
  have hmap : (commutator G).map r = commutator T := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hr, commutator_def]
  have ht : commutator T = ⊤ := by
    apply top_unique
    intro t _
    rw [← hmap]
    exact ⟨i t, ker_le_commutator_of_surjective f hf (hkill t), hri t⟩
  letI : Subsingleton T := subsingleton_of_solvable_perfect ht
  exact fun t => Subsingleton.elim t 1
end Kourovka.CenterQuotients
