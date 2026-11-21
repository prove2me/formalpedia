-- Prove2me | solution 1 for Kourovka.ProductPaths.mixed_term_central
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:42:11.508991+00:00
-- url     : https://prove2.me/submissions/b619ee8a-344d-49ef-b5b8-352f74b17898

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_MixedPaths
import Theorems.Thm_Kourovka_ProductPaths_crossed_word_not_nonabelian
import Theorems.Thm_Kourovka_ProductPaths_axis_axis_same
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_path
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_apply
import Theorems.Thm_Kourovka_ProductPaths_path_append
import Theorems.Thm_Kourovka_ProductPaths_path_central_of_not_nonabelian
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_nil
attribute [local simp] Kourovka.ProductPaths.axis_axis_same
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.iterateHom_apply
attribute [local simp] Kourovka.ProductPaths.path_cons
attribute [local simp] Kourovka.ProductPaths.path_nil



set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    (m : ℕ) (hm : 0 < m)
    (hp : ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw)
    (u v : List Bool) (hu : u.length = m) (hv : v.length = m)
    (j k : Bool) (hjk : j ≠ k) (x : A × B) :
    path f u (axis j (path f v (axis k x))) ∈ Subgroup.center (A × B) := by
  cases v with
  | nil => simp only [List.length_nil] at hv; omega
  | cons i v =>
      rw [axis_path]
      split_ifs with hji
      · subst i
        obtain ⟨y, rfl⟩ := hf x
        have hc := path_central_of_not_nonabelian f hf ((u ++ (j :: v)) ++ [k])
          (crossed_word_not_nonabelian f m hm hp u v j k hu hv hjk) y
        simpa only [path_append, MonoidHom.comp_apply, path_cons, path_nil] using hc
      · simpa only [map_one] using (Subgroup.center (A × B)).one_mem
end Kourovka.ProductPaths
