-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.WordCertificates.encodeRelators_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:24.355825+00:00
-- url     : https://prove2.me/submissions/2fb8bb8f-12ef-41e8-bf0e-9c485cc45e2c

import Definitions.Def_Kourovka_Certificates_PresentationIsomorphism
import Definitions.Def_Kourovka_Presentations_RelatorCodes

set_option autoImplicit true
attribute [refl] MulEquiv.refl
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.WordCertificates
namespace Kourovka.MetabelianEnumeration.WordCertificates
theorem _root_.solution {n : ℕ} (rels : List (FreeGroup (Fin n))) :
    WellFormed (encodeRelators rels) := by
  intro w hw
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hw
  intro letter hletter
  obtain ⟨⟨i, b⟩, _, rfl⟩ := List.mem_map.mp hletter
  exact i.isLt
end Kourovka.MetabelianEnumeration.WordCertificates
