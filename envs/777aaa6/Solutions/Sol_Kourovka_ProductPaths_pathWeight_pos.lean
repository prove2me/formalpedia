-- Prove2me | solution 1 for Kourovka.ProductPaths.pathWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:00.449065+00:00
-- url     : https://prove2.me/submissions/55c892ad-d3ac-42a2-9704-665c1733b5ae

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_pos
import Theorems.Thm_Kourovka_CenterWeight_weight_pos
import Theorems.Thm_Kourovka_SolvableWeight_weight_pos


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B] [IsSolvable A] [IsSolvable B]
    (f : A × B →* A × B) (w : List Bool) (h : Nonabelian f w) :
    0 < pathWeight f w := by
  obtain ⟨x, y, hxy⟩ := h
  apply CenterWeight.weight_pos
  refine ⟨(path f w).rangeRestrict x, (path f w).rangeRestrict y, ?_⟩
  intro hc
  exact hxy (hc.map (path f w).range.subtype)
end Kourovka.ProductPaths
