-- Prove2me | solution 1 for Kourovka.ProductPaths.initialWord_extensionStream
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:41:29.953063+00:00
-- url     : https://prove2.me/submissions/de96378c-872b-4afe-a1d9-fbffdb72c5f8

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_extensionWord_prefix
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
theorem _root_.solution (f : A × B →* A × B) (w : List Bool) (n : ℕ) :
    initialWord n (extensionStream f w) = (extensionWord f w n).take n := by
  apply List.ext_getElem
  · simp only [initialWord, List.length_ofFn, List.length_take, extensionWord_length]
    omega
  · intro i hi hj
    have hin : i < n := by simpa only [initialWord, List.length_ofFn] using hi
    simp only [initialWord, List.getElem_ofFn, FinitePaths.initialSegment,
      List.getElem_take, extensionStream]
    exact (extensionWord_prefix f w (by omega : i + 1 ≤ n)).getElem
      (by rw [extensionWord_length]; omega)
end Kourovka.ProductPaths
