-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.add_abs_le_sum_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:55:44.783191+00:00
-- url     : https://prove2.me/submissions/5268b23e-21c9-4938-a04e-8e5d8241b339

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_sum_box

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (u v : Lattice k) (i : Fin k) :
    |u i + v i| ≤ |(latticeAbs u + latticeAbs v) i| := by
  rw [abs_sum_box]
  exact abs_add_le _ _
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
