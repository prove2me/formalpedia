-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableEnumeration.checkData_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:27:54.284232+00:00
-- url     : https://prove2.me/submissions/deb5fea4-fb7d-426f-8605-af36aec889bb

import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EnumerationCorrectness
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_checked_presentation_metabelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_checkIso_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_metabelian_append
import Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_zero_generators_metabelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_metabelian_surjective


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration
open Kourovka.MetabelianEnumeration.ComputableEnumeration
namespace Kourovka.MetabelianEnumeration.ComputableEnumeration
theorem _root_.solution (p : PresentationCode) (c : Certificate)
    (h : checkData p c = true) : WellFormed p ∧ Metabelian (GroupOf p) := by
  rw [checkData, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  rcases h.2 with hz | ⟨hc, hi⟩
  · exact QuotientCodes.zero_generators_metabelian p hz
  · obtain ⟨_, _, ⟨e⟩⟩ := (ComputableIsomorphism.checkIso_correct (extended c, p)).mp ⟨c.2.2, hi⟩
    exact metabelian_surjective e.toMonoidHom e.surjective
      (QuotientCodes.metabelian_append (source c) c.2.1
        (ComputableCoverSemantics.checked_presentation_metabelian c.1.1 c.1.2 hc))
end Kourovka.MetabelianEnumeration.ComputableEnumeration
