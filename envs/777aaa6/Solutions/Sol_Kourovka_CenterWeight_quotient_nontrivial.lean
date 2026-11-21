-- Prove2me | solution 1 for Kourovka.CenterWeight.quotient_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:10.932311+00:00
-- url     : https://prove2.me/submissions/42fd8135-fe40-4246-b92c-760c05f748be

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight

set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]
namespace Kourovka.CenterWeight
theorem _root_.solution (h : ∃ x y : G, ¬ Commute x y) :
    Nontrivial (G ⧸ Subgroup.center G) := by
  by_contra hn
  letI : Subsingleton (G ⧸ Subgroup.center G) := not_nontrivial_iff_subsingleton.mp hn
  obtain ⟨x, y, hxy⟩ := h
  have hx : x ∈ Subgroup.center G :=
    (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  exact hxy (Subgroup.mem_center_iff.mp hx y).symm
end Kourovka.CenterWeight
