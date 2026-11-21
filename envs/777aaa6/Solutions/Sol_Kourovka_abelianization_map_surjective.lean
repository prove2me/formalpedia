-- Prove2me | solution 1 for Kourovka.abelianization_map_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:29:55.905521+00:00
-- url     : https://prove2.me/submissions/2bcd6530-d61b-4bfc-a478-931d004407b4

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Card
import Definitions.Def_Kourovka_Hopfian

set_option autoImplicit true
open Kourovka
variable {G H : Type*} [Group G] [Group H]
namespace Kourovka
theorem _root_.solution (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (Abelianization.map f) := by
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Abelianization.of x, rfl⟩
end Kourovka
