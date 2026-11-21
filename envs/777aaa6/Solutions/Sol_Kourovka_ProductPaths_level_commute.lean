-- Prove2me | solution 1 for Kourovka.ProductPaths.level_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:38:17.377702+00:00
-- url     : https://prove2.me/submissions/f40b8f3a-17d6-4e31-93c4-cacdbfb66633

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_axes_commute
import Theorems.Thm_Kourovka_ProductPaths_path_nil
import Theorems.Thm_Kourovka_ProductPaths_path_cons
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.path_nil
attribute [local simp] Kourovka.ProductPaths.path_cons

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) :
    ∀ (u v : List Bool), u.length = v.length → u ≠ v →
      ∀ x y : A × B, Commute (path f u x) (path f v y) := by
  intro u
  induction u with
  | nil =>
      intro v hlen hne
      have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
      exact (hne hv.symm).elim
  | cons i u ih =>
      intro v hlen hne x y
      cases v with
      | nil => simp at hlen
      | cons j v =>
          have huv : u.length = v.length := by simpa using hlen
          cases i <;> cases j
          · have hne' : u ≠ v := fun h => hne (by rw [h])
            exact ((ih v huv hne' x y).map f).map (axis false)
          · exact axes_commute (f (path f u x)) (f (path f v y))
          · exact (axes_commute (f (path f v y)) (f (path f u x))).symm
          · have hne' : u ≠ v := fun h => hne (by rw [h])
            exact ((ih v huv hne' x y).map f).map (axis true)
end Kourovka.ProductPaths
