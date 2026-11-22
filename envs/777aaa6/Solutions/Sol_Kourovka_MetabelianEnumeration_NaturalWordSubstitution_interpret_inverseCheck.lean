-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_inverseCheck
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:02:23.998163+00:00
-- url     : https://prove2.me/submissions/4012b7b9-11f1-4985-82b7-fc70f6fbfb83

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_append
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_substitute
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_valid_getD
import Theorems.Thm_Kourovka_MetabelianEnumeration_NaturalWordSubstitution_interpret_singleton_false

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (n m : ℕ) (f g : Images) (hf : WellFormed (m, f))
    (i : ℕ) (hi : i < n) :
    interpretWord n (substitute g (f.getD i []) ++ [(i, false)]) =
      FreeGroup.lift (fun j : Fin m => interpretWord n (g.getD j.val []))
        (interpretWord m (f.getD i [])) * (FreeGroup.of ⟨i, hi⟩)⁻¹ := by
  rw [interpret_append, interpret_substitute m n g _ (valid_getD m f hf i),
    interpret_singleton_false n i hi]
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
