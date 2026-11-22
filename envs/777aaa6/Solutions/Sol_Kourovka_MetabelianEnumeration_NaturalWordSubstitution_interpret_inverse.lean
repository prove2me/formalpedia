-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:31.283504+00:00
-- url     : https://prove2.me/submissions/51d8d3e7-dbe0-4929-ad04-6d8569be5791

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputablePresentations_restrict_mk


set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (n : ℕ) (w : Word) :
    interpretWord n (FreeGroup.invRev w) = (interpretWord n w)⁻¹ := by
  rw [← restrict_mk, ← FreeGroup.inv_mk, map_inv, restrict_mk]
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
