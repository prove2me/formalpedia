-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_singleton_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:46:26.414768+00:00
-- url     : https://prove2.me/submissions/4f4d4307-9a10-40c7-815e-a92fa4e37870

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (n i : ℕ) (hi : i < n) :
    interpretWord n [(i, false)] = (FreeGroup.of ⟨i, hi⟩)⁻¹ := by
  simp [interpretWord, hi]
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
