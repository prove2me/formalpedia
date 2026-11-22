-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.valid_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:42.958871+00:00
-- url     : https://prove2.me/submissions/f9ce368b-30ab-4234-9a7b-ad8bc88ea690

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution {n : ℕ} {w : Word} (h : ValidWord n w) :
    ValidWord n (FreeGroup.invRev w) := by
  intro z hz
  simp only [FreeGroup.invRev, List.mem_reverse, List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact h y hy
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
