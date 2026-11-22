-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.valid_substitute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:33.667195+00:00
-- url     : https://prove2.me/submissions/be88cc96-d021-406c-a29d-1ebc9e6f8c1a

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_inverse

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (m : ℕ) (f : Images) (hf : WellFormed (m, f)) (w : Word) :
    ValidWord m (substitute f w) := by
  intro z hz
  obtain ⟨x, _, hz⟩ := List.mem_flatMap.mp hz
  have hv := valid_getD m f hf x.1
  cases hb : x.2
  · exact valid_inverse hv z (by simpa [hb] using hz)
  · exact hv z (by simpa [hb] using hz)
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
