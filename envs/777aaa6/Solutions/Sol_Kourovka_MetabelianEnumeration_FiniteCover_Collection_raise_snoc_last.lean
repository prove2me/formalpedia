-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:47:58.983499+00:00
-- url     : https://prove2.me/submissions/24fc8f9f-0f69-4b4d-b52e-f7fbe7822a45

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (v : Lattice k) (m : ℤ) :
    raise (Fin.snoc v m) (Fin.last k) = Fin.snoc v (m + 1) := by
  simp only [raise, Fin.snoc_last, Fin.update_snoc_last]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
