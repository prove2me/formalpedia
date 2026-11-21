-- Prove2me | solution 1 for Kourovka.isHopfian_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:33.36447+00:00
-- url     : https://prove2.me/submissions/937a8443-35aa-44ff-bd48-160ee651cd57

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
theorem _root_.solution [Finite G] : IsHopfian G := by
  intro f hf
  exact Finite.injective_iff_surjective.mpr hf
end Kourovka
