-- Prove2me | solution 1 for Kourovka.ProductPaths.livePaths_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:41.558773+00:00
-- url     : https://prove2.me/submissions/6e43a91c-e1ba-41a0-be76-d405b73b57f8

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
import Theorems.Thm_Kourovka_ProductPaths_liveDescendants_finite
import Theorems.Thm_Kourovka_ProductPaths_append_mem_liveDescendants
import Theorems.Thm_Kourovka_ProductPaths_liveDescendants_ncard_le
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
theorem _root_.solution [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) (n : ℕ) :
    (FinitePaths.initialSegment n '' livePaths f).ncard ≤ pathWeight f [] := by
  have hsub : List.ofFn '' (FinitePaths.initialSegment n '' livePaths f) ⊆
      liveDescendants f [] n := by
    rintro w ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    have h := append_mem_liveDescendants f (initialWord n x) [] (by simpa using hx n)
    simpa only [List.nil_append, initialWord, List.length_ofFn] using h
  calc
    (FinitePaths.initialSegment n '' livePaths f).ncard =
        (List.ofFn '' (FinitePaths.initialSegment n '' livePaths f)).ncard :=
      (Set.ncard_image_of_injective _ List.ofFn_injective).symm
    _ ≤ (liveDescendants f [] n).ncard :=
      Set.ncard_le_ncard hsub (liveDescendants_finite f n [])
    _ ≤ pathWeight f [] := liveDescendants_ncard_le f hf n []
end Kourovka.ProductPaths
