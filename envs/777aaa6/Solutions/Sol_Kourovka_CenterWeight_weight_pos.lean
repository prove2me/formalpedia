-- Prove2me | solution 1 for Kourovka.CenterWeight.weight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:52.812756+00:00
-- url     : https://prove2.me/submissions/185e6949-1060-42e5-892e-62984c95f5f2

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight
import Theorems.Thm_Kourovka_CenterWeight_quotient_nontrivial
import Theorems.Thm_Kourovka_AbelianWeight_weight_pos
import Theorems.Thm_Kourovka_SolvableWeight_weight_pos


set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]
namespace Kourovka.CenterWeight
theorem _root_.solution [Group.FG G] [IsSolvable G]
    (h : ∃ x y : G, ¬ Commute x y) : 0 < weight G := by
  letI := quotient_nontrivial h
  exact SolvableWeight.weight_pos _
end Kourovka.CenterWeight
