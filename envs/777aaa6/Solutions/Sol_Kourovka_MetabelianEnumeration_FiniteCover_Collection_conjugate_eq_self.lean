-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T07:48:04.18687+00:00
-- url     : https://prove2.me/submissions/6740ca53-f3b4-4e12-9464-911d9de67970

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {x c : G} (h : Commute c x) : conjugate x c = x := by
  rw [conjugate, mul_assoc, ← h.eq, inv_mul_cancel_left]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
