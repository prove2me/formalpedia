-- Prove2me | solution 1 for Kourovka.ProductPaths.path_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:34:30.366022+00:00
-- url     : https://prove2.me/submissions/8d306708-1f39-49af-9cee-b0d69dd44f74

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_product
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_nil
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.path_cons
attribute [local simp] Kourovka.ProductPaths.path_nil



set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (n : ℕ) (x : A × B) :
    ((allWords n).map (fun w => path f w x)).prod = f^[n] x := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
      simp only [allWords, List.map_append, List.prod_append, List.map_map]
      change ((allWords n).map (fun w => axis false (f (path f w x)))).prod *
        ((allWords n).map (fun w => axis true (f (path f w x)))).prod = _
      have h (i : Bool) := ((axis i).comp f).map_list_prod
        ((allWords n).map (fun w => path f w x))
      simp only [List.map_map, MonoidHom.comp_apply] at h
      change ∀ i, axis i (f ((allWords n).map (fun w => path f w x)).prod) =
        ((allWords n).map (fun w => axis i (f (path f w x)))).prod at h
      rw [← h false, ← h true, ih, axis_product, Function.iterate_succ_apply']
end Kourovka.ProductPaths
