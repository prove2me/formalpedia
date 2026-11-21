-- Prove2me | solution 1 for Kourovka.ProductPaths.liveDescendants_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:55.966723+00:00
-- url     : https://prove2.me/submissions/feebb78e-cd43-4a5e-ac23-1d6277a65eae

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_children_weight_le
import Theorems.Thm_Kourovka_ProductPaths_pathWeight_pos
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
    ∀ w, (liveDescendants f w n).ncard ≤ pathWeight f w := by
  classical
  induction n with
  | zero =>
      intro w
      by_cases h : Nonabelian f w
      · have he : liveDescendants f w 0 = {w} := by
          ext v
          simp only [liveDescendants, Set.mem_setOf_eq, Set.mem_singleton_iff]
          exact ⟨And.left, fun hv => ⟨hv, hv ▸ h⟩⟩
        rw [he, Set.ncard_singleton]
        exact pathWeight_pos f w h
      · have he : liveDescendants f w 0 = ∅ := by
          ext v
          simp only [liveDescendants, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨rfl, hv⟩
          exact h hv
        rw [he, Set.ncard_empty]
        exact Nat.zero_le _
  | succ n ih =>
      intro w
      calc
        (liveDescendants f w (n + 1)).ncard ≤
            (liveDescendants f (w ++ [false]) n).ncard +
              (liveDescendants f (w ++ [true]) n).ncard := Set.ncard_union_le _ _
        _ ≤ pathWeight f (w ++ [false]) + pathWeight f (w ++ [true]) :=
          Nat.add_le_add (ih _) (ih _)
        _ ≤ pathWeight f w := children_weight_le f hf w
end Kourovka.ProductPaths
