-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.interpret_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:34.764197+00:00
-- url     : https://prove2.me/submissions/9922f3ba-20c1-4c62-ac55-55f45609c354

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution (n : ℕ) (z : ℕ × Bool) (w : Word) (hz : z.1 < n) :
    interpretWord n (z :: w) =
      (if z.2 then FreeGroup.of ⟨z.1, hz⟩ else (FreeGroup.of ⟨z.1, hz⟩)⁻¹) *
        interpretWord n w := by simp [interpretWord, hz]
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
