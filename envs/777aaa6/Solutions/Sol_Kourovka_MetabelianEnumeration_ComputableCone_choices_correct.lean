-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCone.choices_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:03:43.342264+00:00
-- url     : https://prove2.me/submissions/43b70648-5011-45c3-94ec-ab5fa39a8663

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_supportRow_iff
import Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_supportRow_iff


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)
namespace Kourovka.MetabelianEnumeration.ComputableCone
theorem _root_.solution (n r : ℕ) (supports : SupportsCode) (x : Fin n → ℝ) :
    (∃ rows ∈ choices r supports, Satisfies n rows x) ↔
      ∀ support ∈ supports, ∃ u ∈ support,
        ConeVerifier.dot (decodeVector n u) x ≤ (1 / 2 : ℝ) ^ r := by
  induction supports with
  | nil => simp [choices, Satisfies]
  | cons support rest ih =>
    rw [List.forall_mem_cons]
    constructor
    · rintro ⟨rows, hrows, hsat⟩
      obtain ⟨u, hu, hrows⟩ := List.mem_flatMap.mp hrows
      obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hrows
      refine ⟨⟨u, hu, (supportRow_iff n r u x).mp (hsat _ List.mem_cons_self)⟩, ?_⟩
      apply ih.mp
      exact ⟨tail, htail, fun row hrow => hsat row (List.mem_cons_of_mem _ hrow)⟩
    · rintro ⟨⟨u, hu, hux⟩, hrest⟩
      obtain ⟨rows, hrows, hsat⟩ := ih.mpr hrest
      refine ⟨supportRow r u :: rows,
        List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨rows, hrows, rfl⟩⟩, ?_⟩
      intro row hrow
      rcases List.mem_cons.mp hrow with rfl | hrow
      · exact (supportRow_iff n r u x).mpr hux
      · exact hsat row hrow
end Kourovka.MetabelianEnumeration.ComputableCone
