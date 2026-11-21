-- Prove2me | solution 1 for Kourovka.IsHopfian.of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:30.470187+00:00
-- url     : https://prove2.me/submissions/e8828035-d226-405c-b498-cda6ce44fc4f

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
namespace IsHopfian
theorem _root_.solution (hG : IsHopfian G) (e : G ≃* H) : IsHopfian H := by
  intro f hf
  let g := e.symm.toMonoidHom.comp (f.comp e.toMonoidHom)
  have hg : Function.Surjective g :=
    e.symm.surjective.comp (hf.comp e.surjective)
  have hi := hG g hg
  intro x y hxy
  apply e.symm.injective
  apply hi
  simpa [g] using congrArg e.symm hxy
end IsHopfian
end Kourovka
