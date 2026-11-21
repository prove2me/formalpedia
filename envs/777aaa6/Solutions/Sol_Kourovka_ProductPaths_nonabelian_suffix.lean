-- Prove2me | solution 1 for Kourovka.ProductPaths.nonabelian_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:30.639+00:00
-- url     : https://prove2.me/submissions/373cf1b0-f79a-49cc-bf36-54e2403a8053

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
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
theorem _root_.solution (f : A × B →* A × B) (u v : List Bool)
    (h : Nonabelian f (u ++ v)) : Nonabelian f v := by
  obtain ⟨x, y, h⟩ := h
  refine ⟨x, y, ?_⟩
  intro hc
  apply h
  simpa only [path_append, MonoidHom.comp_apply] using hc.map (path f u)
end Kourovka.ProductPaths
