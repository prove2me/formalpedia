-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.finite_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:59.711166+00:00
-- url     : https://prove2.me/submissions/1422e49f-b43e-43e4-a181-e044eadd887d

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin
import Theorems.Thm_Kourovka_MetabelianEnumeration_FourierMotzkin_exists_common_lower_bound

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {K : Type*} [LinearOrder K] [Zero K]
    (lower upper : List K) :
    (∃ t : K, (∀ l ∈ lower, l ≤ t) ∧ (∀ u ∈ upper, t ≤ u)) ↔
      ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u := by
  constructor
  · rintro ⟨t, hl, hu⟩ l hl' u hu'
    exact (hl l hl').trans (hu u hu')
  · induction lower with
    | nil =>
      intro _
      obtain ⟨t, ht⟩ := exists_common_lower_bound upper
      exact ⟨t, by simp, ht⟩
    | cons l lower ih =>
      intro h
      obtain ⟨t, ht, htu⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      refine ⟨max l t, ?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact le_max_left _ _
        · exact (ht a ha).trans (le_max_right _ _)
      · intro u hu
        exact max_le (h l List.mem_cons_self u hu) (htu u hu)
end Kourovka.MetabelianEnumeration.FourierMotzkin
