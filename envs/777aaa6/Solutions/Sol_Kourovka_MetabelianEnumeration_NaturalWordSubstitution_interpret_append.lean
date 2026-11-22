-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:45:01.487638+00:00
-- url     : https://prove2.me/submissions/50f1cecd-bb0f-4198-9d78-ebeb8fe712ea

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (n : ℕ) (u v : Word) :
    interpretWord n (u ++ v) = interpretWord n u * interpretWord n v := by
  simp only [interpretWord, List.map_append, List.prod_append]
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
