-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.NaturalWordSubstitution.valid_encode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:37.735947+00:00
-- url     : https://prove2.me/submissions/18f03a2e-1f41-44ec-9af1-3d7eee3f7171

import Definitions.Def_Kourovka_Computability_ComputablePresentations
import Definitions.Def_Kourovka_Presentations_RelatorCodes
import Mathlib.Data.List.GetD
import Definitions.Def_Kourovka_Certificates_NaturalWordSubstitution

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.NaturalWordSubstitution
open ComputableWords ComputablePresentations
namespace Kourovka.MetabelianEnumeration.NaturalWordSubstitution
theorem _root_.solution {n : ℕ} (w : WordCertificates.Word n) :
    ValidWord n (WordCertificates.encodeWord w) := by
  intro z hz
  obtain ⟨⟨i, b⟩, _, rfl⟩ := List.mem_map.mp hz
  exact i.isLt
end Kourovka.MetabelianEnumeration.NaturalWordSubstitution
