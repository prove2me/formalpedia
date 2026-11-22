-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:49:45.471606+00:00
-- url     : https://prove2.me/submissions/38fc9fd1-3efa-4c2d-88be-c44e0a3d4776

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionGeometry
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last



set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (v w : Lattice k) :
    euclidean (v + w) = euclidean v + euclidean w := by
  ext i; simp [euclidean]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
