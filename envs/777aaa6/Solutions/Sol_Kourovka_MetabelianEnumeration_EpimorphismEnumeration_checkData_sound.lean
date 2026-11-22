-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.EpimorphismEnumeration.checkData_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:26:35.395384+00:00
-- url     : https://prove2.me/submissions/dc6701b1-3baf-400b-a2e2-7b0a43fcefc2

import Definitions.Def_Kourovka_Certificates_EpimorphismSemantics
import Definitions.Def_Kourovka_Enumeration_EnumerationCofinality
import Definitions.Def_Kourovka_Covers_ComputableCoverSemantics
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Definitions.Def_Kourovka_Enumeration_EpimorphismEnumeration
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverSemantics_checked_presentation_metabelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableEpimorphism_checkEpi_correct
import Theorems.Thm_Kourovka_MetabelianEnumeration_QuotientCodes_zero_generators_metabelian
import Theorems.Thm_Kourovka_MetabelianEnumeration_metabelian_surjective


set_option autoImplicit true
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.EpimorphismEnumeration
namespace Kourovka.MetabelianEnumeration.EpimorphismEnumeration
theorem _root_.solution (p : PresentationCode) (c : Certificate)
    (h : checkData p c = true) : WellFormed p ∧ Metabelian (GroupOf p) := by
  rw [checkData, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  -- The zero-generator group is trivial; every other accepted input is a quotient of a cover.
  rcases h.2 with hz | ⟨hc, he⟩
  · exact QuotientCodes.zero_generators_metabelian p hz
  · obtain ⟨_, _, f, hf⟩ := (ComputableEpimorphism.checkEpi_correct (source c, p)).mp ⟨c.2, he⟩
    exact metabelian_surjective f hf
      (ComputableCoverSemantics.checked_presentation_metabelian c.1.1 c.1.2 hc)
end Kourovka.MetabelianEnumeration.EpimorphismEnumeration
