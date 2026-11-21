-- Prove2me | solution 1 for Kourovka.SolvableWeight.abelianization_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:54.249305+00:00
-- url     : https://prove2.me/submissions/b4197429-57c8-4f60-907e-82bef103e35d

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
import Theorems.Thm_Kourovka_subsingleton_of_solvable_perfect


set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]
namespace Kourovka.SolvableWeight
theorem _root_.solution [IsSolvable G] [Nontrivial G] :
    Nontrivial (Abelianization G) := by
  by_contra h
  letI : Subsingleton (Abelianization G) := not_nontrivial_iff_subsingleton.mp h
  have hp : commutator G = ⊤ := by
    rw [← Abelianization.ker_of]
    apply top_unique
    intro g _
    exact Subsingleton.elim _ _
  letI : Subsingleton G := subsingleton_of_solvable_perfect hp
  exact not_subsingleton G inferInstance
end Kourovka.SolvableWeight
