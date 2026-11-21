-- Prove2me | Definitions.Def_Kourovka_PathExtension
-- name    : Kourovka_PathExtension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T03:32:44.694784+00:00
-- url     : https://prove2.me/theorems/f9af4c59-d0fa-47ea-b3db-2c9ffbb61c6a
-- title:
--   Path Extension
-- statement:
--   Definitions and structural lemmas for Path Extension, from Achyuth Jayadevan's pinned Direct products of soluble Hopfian groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Theorems.Thm_Kourovka_ProductPaths_axis_false
import Theorems.Thm_Kourovka_ProductPaths_axis_true
import Theorems.Thm_Kourovka_ProductPaths_path_cons
import Theorems.Thm_Kourovka_ProductPaths_path_nil
attribute [local simp] Kourovka.ProductPaths.axis_false
attribute [local simp] Kourovka.ProductPaths.axis_true
attribute [local simp] Kourovka.ProductPaths.path_cons
attribute [local simp] Kourovka.ProductPaths.path_nil


set_option autoImplicit true
namespace Kourovka
namespace ProductPaths
variable {A B : Type*} [Group A] [Group B]
noncomputable def extendWord (f : A × B →* A × B) (w : List Bool) : List Bool := by
  classical
  exact w ++ [if Nonabelian f (w ++ [false]) then false else true]
theorem extendWord_length (f : A × B →* A × B) (w : List Bool) :
    (extendWord f w).length = w.length + 1 := by
  classical
  simp only [extendWord, List.length_append, List.length_singleton]
noncomputable def extensionWord (f : A × B →* A × B) (w : List Bool) (n : ℕ) : List Bool :=
  (extendWord f)^[n] w
theorem extensionWord_length (f : A × B →* A × B) (w : List Bool) (n : ℕ) :
    (extensionWord f w n).length = w.length + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((extendWord f)^[n + 1] w).length = _
      rw [Function.iterate_succ_apply']
      rw [extendWord_length, ← extensionWord, ih]
      omega
noncomputable def extensionStream (f : A × B →* A × B) (w : List Bool) (n : ℕ) : Bool :=
  (extensionWord f w (n + 1))[n]'(by rw [extensionWord_length]; omega)
end ProductPaths
end Kourovka


