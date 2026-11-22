-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverBounds.presentation_wellFormed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:18:44.805704+00:00
-- url     : https://prove2.me/submissions/dae5826d-1d83-4fd8-955a-f61443fbe147

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_relators_mem

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords
namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds
theorem _root_.solution (data : DatumCode) (R : ℕ) :
    WellFormed (presentation data R) := by
  intro w hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
  exact relators_mem data R r hr
end Kourovka.MetabelianEnumeration.ComputableCoverBounds
