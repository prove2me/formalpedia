-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:53:43.995176+00:00
-- url     : https://prove2.me/submissions/aa39d45f-e68e-4a4d-9419-e2b38e1880d4

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
theorem _root_.solution {k : ℕ} (t : Fin (k + 1) → G) (v : Lattice (k + 1)) :
    orderedWord t v = orderedWord (fun i => t i.castSucc) (fun i => v i.castSucc) *
      t (Fin.last k) ^ v (Fin.last k) := by
  simp only [orderedWord, List.ofFn_succ', List.prod_concat]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
