-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverBounds.ordered_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:01:14.249731+00:00
-- url     : https://prove2.me/submissions/2f1bd797-9aa4-4303-a543-54f578f2f48a

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_of_mem

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords
namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds
theorem _root_.solution {k n : ℕ} (hk : k ≤ n) (v : List ℤ) : ordered k v ∈ bounded n := by
  apply (bounded n).list_prod_mem
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact (bounded n).zpow_mem (of_mem ((List.mem_range.mp hi).trans_le hk)) _
end Kourovka.MetabelianEnumeration.ComputableCoverBounds
