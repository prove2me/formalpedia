-- Prove2me | solution 1 for Kourovka.isHopfian_of_commGroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:15.67648+00:00
-- url     : https://prove2.me/submissions/44177f69-8224-4ba5-9b8a-835c4b88c169

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
theorem _root_.solution (A : Type*) [CommGroup A] [Group.FG A] :
    IsHopfian A := by
  intro f hf
  letI : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  exact IsNoetherian.injective_of_surjective_endomorphism f.toAdditive.toIntLinearMap hf
end Kourovka
