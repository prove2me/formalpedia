-- Prove2me | solution 1 for Kourovka.ProductPaths.axis_path
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:24.979063+00:00
-- url     : https://prove2.me/submissions/2f9d7b4d-279b-4aaf-90ce-440323fbcf53

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion
import Theorems.Thm_Kourovka_ProductPaths_axis_axis_same
import Theorems.Thm_Kourovka_ProductPaths_axis_axis_ne
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_nil
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.path_cons
attribute [local simp] Kourovka.ProductPaths.path_nil


attribute [local simp] Kourovka.ProductPaths.axis_axis_same

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (i j : Bool) (f : A × B →* A × B) (w : List Bool) (x : A × B) :
    axis i (path f (j :: w) x) = if i = j then path f (j :: w) x else 1 := by
  rw [path_cons]
  split_ifs with h
  · subst j; exact axis_axis_same i _
  · exact axis_axis_ne i j h _
end Kourovka.ProductPaths
