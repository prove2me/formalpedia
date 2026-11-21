-- Prove2me | solution 1 for Kourovka.ProductPaths.children_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:11.447297+00:00
-- url     : https://prove2.me/submissions/9f4e68ab-1f50-4d93-a459-496a2234bd57

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_axes_commute
import Theorems.Thm_Kourovka_ProductPaths_path_nil
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_append
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.path_nil
attribute [local simp] Kourovka.ProductPaths.path_cons

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (w : List Bool) (x y : A × B) :
    Commute (path f (w ++ [false]) x) (path f (w ++ [true]) y) := by
  simp only [path_append, MonoidHom.comp_apply, path_cons, path_nil]
  exact (axes_commute (f x) (f y)).map (path f w)
end Kourovka.ProductPaths
