-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:44:42.771681+00:00
-- url     : https://prove2.me/submissions/b20013c1-808b-4f19-98b7-29aeaffa772b

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {k : ℕ} (v : Lattice k) (m : ℤ) (i : Fin k) :
    raise (Fin.snoc v m) i.castSucc = Fin.snoc (raise v i) m := by
  simp only [raise, Fin.snoc_castSucc, Fin.snoc_update]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
