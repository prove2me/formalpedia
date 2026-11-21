-- Prove2me | solution 1 for Kourovka.ProductPaths.allWords_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:34:55.980282+00:00
-- url     : https://prove2.me/submissions/da136a95-6370-41b2-b1f0-14e66e7351d3

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion
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
theorem _root_.solution (n : ℕ) : ∀ w ∈ allWords n, w.length = n := by
  induction n with
  | zero =>
      intro w hw
      have he : w = [] := List.mem_singleton.mp hw
      subst w
      rfl
  | succ n ih =>
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        simp only [List.length_cons, ih v hv]
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        simp only [List.length_cons, ih v hv]
end Kourovka.ProductPaths
