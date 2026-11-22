-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_sum_box
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:54:46.354311+00:00
-- url     : https://prove2.me/submissions/64421a91-bc9e-4728-8c23-15df70266d4e

import Definitions.Def_Kourovka_Collection_CollectionFinite
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Definitions.Def_Kourovka_Collection_CollectionRadius

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (u v : Lattice k) (i : Fin k) :
    |(latticeAbs u + latticeAbs v) i| = |u i| + |v i| := by
  exact abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
