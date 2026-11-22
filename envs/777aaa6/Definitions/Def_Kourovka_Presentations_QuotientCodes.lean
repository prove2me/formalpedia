-- Prove2me | Definitions.Def_Kourovka_Presentations_QuotientCodes
-- name    : Kourovka_Presentations_QuotientCodes
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:48:18.72559+00:00
-- url     : https://prove2.me/theorems/8ceb4b97-bbfe-488e-b2c3-fe634695711d
-- title:
--   Quotient Codes
-- statement:
--   Definitions and structural lemmas for Quotient Codes, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Presentations/QuotientCodes.lean

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD


set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates
def appendRelators (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    PresentationCode := (p.1, p.2 ++ extra)
theorem relations_subset_append (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    relations p ⊆ relations (appendRelators p extra) := by
  intro r hr
  change r ∈ (p.2 ++ extra).map (interpretWord p.1)
  rw [List.map_append]
  exact List.mem_append_left _ hr
def quotientHom (p : PresentationCode) (extra : List (List (ℕ × Bool))) :
    GroupOf p →* GroupOf (appendRelators p extra) :=
  QuotientGroup.map (Subgroup.normalClosure (relations p))
    (Subgroup.normalClosure (relations (appendRelators p extra))) (MonoidHom.id _) (by
      simpa only [Subgroup.comap_id] using
        Subgroup.normalClosure_mono (relations_subset_append p extra))
end Kourovka.MetabelianEnumeration.QuotientCodes


