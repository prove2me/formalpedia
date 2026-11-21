-- Prove2me | solution 1 for Kourovka.ProductPaths.crossed_word_not_nonabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:08.669863+00:00
-- url     : https://prove2.me/submissions/e8804168-a856-49ae-837e-97cd177a18c7

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_MixedPaths
import Theorems.Thm_Kourovka_ProductPaths_axis_axis_same
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_iterateHom_apply
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
theorem _root_.solution (f : A × B →* A × B) (m : ℕ) (hm : 0 < m)
    (hp : ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw)
    (u v : List Bool) (j k : Bool) (hu : u.length = m) (hv : (j :: v).length = m)
    (hjk : j ≠ k) : ¬ Nonabelian f ((u ++ (j :: v)) ++ [k]) := by
  intro hn
  have hlen : 2 * m < ((u ++ (j :: v)) ++ [k]).length := by
    simp only [List.length_append, List.length_singleton, hu, hv]
    omega
  have he := hp _ hlen hn
  have hm2 : m < m + m := by omega
  have hm0 : ¬ m < m := by omega
  have h2 : ¬ 2 * m < m + m := by omega
  simp only [List.getElem_append, List.length_append, hu, hv, hm2, hm0, h2,
    dif_pos, Nat.sub_self, List.getElem_cons_zero] at he
  have hz : 2 * m - (m + m) = 0 := by omega
  simp only [hz, List.getElem_cons_zero] at he
  exact hjk he
end Kourovka.ProductPaths
