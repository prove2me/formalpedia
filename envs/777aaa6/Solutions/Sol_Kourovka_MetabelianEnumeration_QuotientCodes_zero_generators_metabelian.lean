-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.QuotientCodes.zero_generators_metabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:56:32.611819+00:00
-- url     : https://prove2.me/submissions/d49b7d8e-6020-426d-9d9b-180f52b4bc38

import Definitions.Def_Kourovka_Certificates_IsomorphismSemantics
import Definitions.Def_Kourovka_Presentations_FiniteQuotient
import Definitions.Def_Kourovka_Presentations_QuotientCodes
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_encodeImages_length
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableIsomorphism_interpret_encodeImages_getD
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.encodeImages_length
attribute [local simp] Kourovka.MetabelianEnumeration.ComputableIsomorphism.interpret_encodeImages_getD



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.QuotientCodes
open NaturalWordSubstitution WordCertificates
namespace Kourovka.MetabelianEnumeration.QuotientCodes
theorem _root_.solution (p : PresentationCode) (h : p.1 = 0) :
    Metabelian (GroupOf p) := by
  rcases p with ⟨n, rels⟩
  dsimp only at h
  subst n
  have hone (x : GroupOf (0, rels)) : x = 1 := by
    exact Subgroup.mem_bot.mp (PresentedGroup.generated_by (relations (0, rels)) ⊥
      (fun i => Fin.elim0 i) x)
  letI : Subsingleton (GroupOf (0, rels)) := ⟨fun x y => (hone x).trans (hone y).symm⟩
  intro a b c d
  change _ * _ = _ * _
  exact Subsingleton.elim _ _
end Kourovka.MetabelianEnumeration.QuotientCodes
