-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverBounds.relators_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:35.327342+00:00
-- url     : https://prove2.me/submissions/5450c3f2-63dd-4b61-9a0d-b20d2dc7db4b

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_of_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_conjugate_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_rightComm_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_ordered_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_polynomial_mem

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords
namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds
theorem _root_.solution (data : DatumCode) (R : ℕ) :
    ∀ w ∈ relators data R, w ∈ bounded (dimension data + alphabet data) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
      have hi' := List.mem_range.mp hi
      have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
      apply (bounded _).mul_mem
      · exact rightComm_mem (of_mem (by omega)) (of_mem (by omega))
      · apply (bounded _).inv_mem
        apply of_mem
        exact Nat.add_lt_add_left (Nat.mod_lt _ (Nat.succ_pos _)) _
    · obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨j, hj, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw
      have hi' := List.mem_range.mp hi
      have hj' := List.mem_range.mp hj
      apply rightComm_mem (of_mem (by omega))
      exact conjugate_mem (of_mem (by omega)) (ordered_mem (Nat.le_add_right _ _) _)
  · obtain ⟨i, hi, hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hw
    have hi' := List.mem_range.mp hi
    have hx := of_mem (n := dimension data + alphabet data)
      (i := dimension data + i) (by omega)
    exact (bounded _).mul_mem ((bounded _).inv_mem hx)
      (polynomial_mem (Nat.le_add_right _ _) hx p)
end Kourovka.MetabelianEnumeration.ComputableCoverBounds
