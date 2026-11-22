-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:29.127944+00:00
-- url     : https://prove2.me/submissions/f283be2e-e1cc-4fda-b73e-7fa60f11fd25

import Definitions.Def_Kourovka_Collection_Collection
import Definitions.Def_Kourovka_Collection_CollectionFinite
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last


attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_nil

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (t : Fin k → G) (w : Lattice k) :
    blockWord t w (List.finRange k) = orderedWord t w := by
  simp [blockWord, orderedWord, List.ofFn_eq_map]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
