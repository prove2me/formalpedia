-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.QuotientCodes.finite_quotient_codes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:08:55.368756+00:00
-- url     : https://prove2.me/submissions/b432e82b-13cf-4986-bd3b-29734b7cd488

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_encodeRelators_wellFormed
import Theorems.Thm_Kourovka_MetabelianEnumeration_WordCertificates_finite_relator_quotient_of_surjection
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates
namespace Kourovka.MetabelianEnumeration.QuotientCodes
theorem _root_.solution (p q : PresentationCode) (hp : WellFormed p)
    (_hq : WellFormed q) (f : GroupOf p →* GroupOf q) (hf : Function.Surjective f) :
    ∃ extra : List (List (ℕ × Bool)), WellFormed (appendRelators p extra) ∧
      Nonempty (GroupOf (appendRelators p extra) ≃* GroupOf q) := by
  classical
  obtain ⟨rels, ⟨e⟩⟩ := finite_relator_quotient_of_surjection
    (p.2.map (interpretWord p.1)) (q.2.map (interpretWord q.1)) f hf
  let extra := (encodeRelators rels).2
  have he : WellFormed (p.1, extra) := encodeRelators_wellFormed rels
  have hm : extra.map (interpretWord p.1) = rels := by
    simp [extra, encodeRelators, List.map_map, Function.comp_def,
      interpret_encodeWord, FreeGroup.mk_toWord]
  have hr : relations (appendRelators p extra) =
      relSet (p.2.map (interpretWord p.1) ++ rels) := by
    simp only [relations, appendRelators, List.map_append, hm, relSet]
    rfl
  have ei : GroupOf (appendRelators p extra) ≃*
      PresentedGroup (relSet (p.2.map (interpretWord p.1) ++ rels)) := by
    change PresentedGroup (relations (appendRelators p extra)) ≃* _
    rw [hr]
    exact MulEquiv.refl _
  refine ⟨extra, ?_, ⟨ei.trans e⟩⟩
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact hp w hw
  · exact he w hw
end Kourovka.MetabelianEnumeration.QuotientCodes
