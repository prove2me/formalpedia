-- Prove2me | solution 1 for Kourovka.ProductPaths.path_central_of_not_nonabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:07.17971+00:00
-- url     : https://prove2.me/submissions/57dd6000-da3d-4573-bd22-2b0129fcc0bb

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion
import Theorems.Thm_Kourovka_ProductPaths_allWords_length
import Theorems.Thm_Kourovka_ProductPaths_path_expansion
import Theorems.Thm_Kourovka_ProductPaths_level_commute


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B)
    (hf : Function.Surjective f) (w : List Bool) (hn : ¬ Nonabelian f w) (x : A × B) :
    path f w x ∈ Subgroup.center (A × B) := by
  rw [Subgroup.mem_center_iff]
  intro z
  obtain ⟨y, rfl⟩ := (hf.iterate w.length) z
  rw [← path_expansion]
  apply Commute.list_prod_left
  intro t ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
  by_cases he : v = w
  · subst v
    by_contra hc
    exact hn ⟨y, x, hc⟩
  · exact level_commute f v w (allWords_length _ _ hv) he y x
end Kourovka.ProductPaths
