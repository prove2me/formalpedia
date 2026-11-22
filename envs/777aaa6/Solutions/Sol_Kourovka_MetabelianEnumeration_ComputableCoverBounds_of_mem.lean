-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverBounds.of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:59:52.769957+00:00
-- url     : https://prove2.me/submissions/498df729-e304-4452-bbfb-e1d501225fe7

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords
namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds
theorem _root_.solution {n i : ℕ} (h : i < n) : FreeGroup.of i ∈ bounded n := by
  intro letter hletter
  obtain rfl := List.mem_singleton.mp (FreeGroup.toWord_of i ▸ hletter)
  exact h
end Kourovka.MetabelianEnumeration.ComputableCoverBounds
