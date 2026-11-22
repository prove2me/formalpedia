-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.ComputableCoverBounds.polynomial_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:16:23.007972+00:00
-- url     : https://prove2.me/submissions/234b6119-3a33-4575-8610-1772dca594a6

import Definitions.Def_Kourovka_Covers_ComputableCoverWords
import Definitions.Def_Kourovka_Covers_ComputableCoverBounds
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_conjugate_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCoverBounds_ordered_mem

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCoverBounds
open ComputableCoverData ComputableCoverWords
namespace Kourovka.MetabelianEnumeration.ComputableCoverBounds
theorem _root_.solution {k n : ℕ} (hk : k ≤ n) {x : WordGroup}
    (hx : x ∈ bounded n) (p : PolynomialCode) : polynomial k x p ∈ bounded n := by
  apply (bounded n).list_prod_mem
  intro w hw
  obtain ⟨term, _, rfl⟩ := List.mem_map.mp hw
  apply conjugate_mem ((bounded n).zpow_mem hx _)
  cases p.1
  · exact (bounded n).inv_mem (ordered_mem hk _)
  · exact ordered_mem hk _
end Kourovka.MetabelianEnumeration.ComputableCoverBounds
