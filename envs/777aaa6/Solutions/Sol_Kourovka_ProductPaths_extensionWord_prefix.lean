-- Prove2me | solution 1 for Kourovka.ProductPaths.extensionWord_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:31.375917+00:00
-- url     : https://prove2.me/submissions/57b58590-1054-4a40-b029-ea29badc8124

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_prefix_extendWord

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (w : List Bool)
    {n m : ℕ} (h : n ≤ m) : extensionWord f w n <+: extensionWord f w m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact List.prefix_refl _
  | succ k ih =>
      apply ih.trans
      change extensionWord f w (n + k) <+: (extendWord f)^[n + (k + 1)] w
      rw [show n + (k + 1) = (n + k) + 1 by omega, Function.iterate_succ_apply']
      exact prefix_extendWord f _
end Kourovka.ProductPaths
