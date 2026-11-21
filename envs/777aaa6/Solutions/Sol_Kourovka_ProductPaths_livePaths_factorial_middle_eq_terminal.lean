-- Prove2me | solution 1 for Kourovka.ProductPaths.livePaths_factorial_middle_eq_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:43:27.089555+00:00
-- url     : https://prove2.me/submissions/bd4474e3-7349-42e9-9010-f6bf9799b22b

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
import Theorems.Thm_Kourovka_ProductPaths_livePaths_prefix_bound
import Theorems.Thm_Kourovka_ProductPaths_livePaths_shift
import Theorems.Thm_Kourovka_FinitePaths_factorial_middle_eq_terminal_of_bounded_prefixes
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_pathWeight_nil
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
    (hf : Function.Surjective f) :
    ∀ x ∈ livePaths f,
      x (CenterWeight.weight (A × B)).factorial =
        x (2 * (CenterWeight.weight (A × B)).factorial) :=
  FinitePaths.factorial_middle_eq_terminal_of_bounded_prefixes
    (livePaths f) (CenterWeight.weight (A × B))
    (fun n => by simpa only [pathWeight_nil] using livePaths_prefix_bound f hf n)
    (livePaths_shift f)
end Kourovka.ProductPaths
