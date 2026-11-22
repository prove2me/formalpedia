-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_le_sum_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:55:44.392177+00:00
-- url     : https://prove2.me/submissions/8937e66a-84b9-4dca-afff-4718f14abc7c

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_sum_box

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (u v : Lattice k) (i : Fin k) :
    |u i| ≤ |(latticeAbs u + latticeAbs v) i| := by
  rw [abs_sum_box]
  exact le_add_of_nonneg_right (abs_nonneg _)
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
