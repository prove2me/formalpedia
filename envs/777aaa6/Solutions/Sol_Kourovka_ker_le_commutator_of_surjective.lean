-- Prove2me | solution 1 for Kourovka.ker_le_commutator_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:36:40.67648+00:00
-- url     : https://prove2.me/submissions/bbaf68c5-e3da-4ac3-b1b3-532a5efca71b

import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Solvable
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Fintype.Card
import Definitions.Def_Kourovka_Hopfian
import Theorems.Thm_Kourovka_isHopfian_of_commGroup
import Theorems.Thm_Kourovka_abelianization_map_surjective

set_option autoImplicit true
open Kourovka
variable {G H : Type*} [Group G] [Group H]
namespace Kourovka
theorem _root_.solution [Group.FG G] (f : G →* G)
    (hf : Function.Surjective f) : f.ker ≤ commutator G := by
  letI : Group.FG (Abelianization G) :=
    Group.fg_of_surjective (f := Abelianization.of) QuotientGroup.mk_surjective
  have hi := isHopfian_of_commGroup (Abelianization G)
    (Abelianization.map f) (abelianization_map_surjective f hf)
  intro x hx
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  apply hi
  simpa using congrArg (Abelianization.of : G → Abelianization G) hx
end Kourovka
