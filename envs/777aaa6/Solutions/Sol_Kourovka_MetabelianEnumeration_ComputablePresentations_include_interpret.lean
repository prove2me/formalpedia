-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputablePresentations.include_interpret
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:08.132176+00:00
-- url     : https://prove2.me/submissions/20c3a83c-b728-4fcb-90b6-91e8e3bb3626

import Definitions.Def_Kourovka_Computability_ComputableClosure
import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_restrict_mk

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputablePresentations
open ComputableWords
namespace Kourovka.MetabelianEnumeration.ComputablePresentations
theorem _root_.solution (n : ℕ) (w : List (ℕ × Bool))
    (hw : ∀ letter ∈ w, letter.1 < n) :
    includeGenerators n (interpretWord n w) = FreeGroup.mk w := by
  rw [← restrict_mk]
  have hmk : (includeGenerators n).comp (restrictGenerators n) (FreeGroup.mk w) =
      (FreeGroup.lift (fun i : ℕ => FreeGroup.of i)) (FreeGroup.mk w) := by
    simp only [FreeGroup.lift_mk, restrictGenerators, MonoidHom.comp_apply,
      map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro letter hletter
    cases hb : letter.2 <;> simp [hw letter hletter, includeGenerators, hb]
  have hid : (FreeGroup.lift (fun i : ℕ => FreeGroup.of i)) = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro i
    simp
  simpa only [hid, MonoidHom.id_apply, MonoidHom.comp_apply] using hmk
end Kourovka.MetabelianEnumeration.ComputablePresentations
