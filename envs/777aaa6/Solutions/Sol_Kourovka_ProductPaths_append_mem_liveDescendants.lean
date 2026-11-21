-- Prove2me | solution 1 for Kourovka.ProductPaths.append_mem_liveDescendants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:13.955188+00:00
-- url     : https://prove2.me/submissions/e1cd2f69-0608-4317-aae6-671609fef40f

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
import Theorems.Thm_Kourovka_ProductPaths_axis_false
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
theorem _root_.solution (f : A × B →* A × B) (u : List Bool) :
    ∀ w, Nonabelian f (w ++ u) → w ++ u ∈ liveDescendants f w u.length := by
  induction u with
  | nil =>
      intro w h
      exact ⟨List.append_nil w, h⟩
  | cons i u ih =>
      intro w h
      have ha : w ++ i :: u = (w ++ [i]) ++ u := by simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [ha] at h ⊢
      cases i
      · exact Or.inl (ih (w ++ [false]) h)
      · exact Or.inr (ih (w ++ [true]) h)
end Kourovka.ProductPaths
