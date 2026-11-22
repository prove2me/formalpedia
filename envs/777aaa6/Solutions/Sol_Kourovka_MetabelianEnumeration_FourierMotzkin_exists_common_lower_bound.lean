-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.exists_common_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:51:42.643032+00:00
-- url     : https://prove2.me/submissions/bcde83be-ee0e-4cde-a500-e2611f33f23a

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
theorem _root_.solution {K : Type*} [LinearOrder K] [Zero K]
    (upper : List K) : ∃ t : K, ∀ u ∈ upper, t ≤ u := by
  induction upper with
  | nil => exact ⟨0, by simp⟩
  | cons u upper ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨min u t, ?_⟩
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ht v hv)
end Kourovka.MetabelianEnumeration.FourierMotzkin
