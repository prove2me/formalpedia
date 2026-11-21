-- Prove2me | solution 1 for Kourovka.ProductPaths.children_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:47.050935+00:00
-- url     : https://prove2.me/submissions/c59fef9c-7ceb-4cba-bfcd-58a7319b54b8

import Definitions.Def_Kourovka_CenterWeight
import Definitions.Def_Kourovka_Paths
import Definitions.Def_Kourovka_PathWeight
import Theorems.Thm_Kourovka_ProductPaths_branch_commute
import Theorems.Thm_Kourovka_ProductPaths_branch_cover
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr
import Theorems.Thm_Kourovka_CenterWeight_split
import Theorems.Thm_Kourovka_CenterWeight_weight_congr
import Theorems.Thm_Kourovka_SolvableWeight_weight_congr


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f) (w : List Bool) :
    pathWeight f (w ++ [false]) + pathWeight f (w ++ [true]) ≤ pathWeight f w := by
  have h := CenterWeight.split (branch (path f w) false).range
    (branch (path f w) true).range (branch_commute (path f w)) (branch_cover (path f w))
  rw [CenterWeight.weight_congr (branchEquiv f hf w false),
    CenterWeight.weight_congr (branchEquiv f hf w true)] at h
  exact h
end Kourovka.ProductPaths
