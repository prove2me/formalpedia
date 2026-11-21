-- Prove2me | solution 1 for Kourovka.centralCorrection_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:54.842405+00:00
-- url     : https://prove2.me/submissions/6f47d9f1-8f1f-4527-a31d-cca105e7e14f

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
import Theorems.Thm_Kourovka_surjective_of_derived_and_abelianization
import Theorems.Thm_Kourovka_centralCorrection_eq_on_commutator


set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
namespace Kourovka
theorem _root_.solution (u : G →* G) (h : G →* Subgroup.center G)
    (hder : ∀ y ∈ commutator G, ∃ x ∈ commutator G, u x = y)
    (hab : Function.Surjective (Abelianization.map (centralCorrection u h))) :
    Function.Surjective (centralCorrection u h) := by
  apply surjective_of_derived_and_abelianization _ _ hab
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hder y hy
  exact ⟨x, hx, (centralCorrection_eq_on_commutator u h hx).trans hxy⟩
end Kourovka
