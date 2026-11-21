-- Prove2me | solution 1 for Kourovka.ProductPaths.children_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:24.557737+00:00
-- url     : https://prove2.me/submissions/71361d84-5046-4340-a754-df529e82328a

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_axis_product
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
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (x : A × B) :
    ∃ y z, path f (w ++ [false]) y * path f (w ++ [true]) z = path f w x := by
  obtain ⟨y, hy⟩ := hf x
  refine ⟨y, y, ?_⟩
  simp only [path_append, MonoidHom.comp_apply, path_cons, path_nil]
  rw [← map_mul, axis_product, hy]
end Kourovka.ProductPaths
