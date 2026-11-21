-- Prove2me | solution 1 for Kourovka.ProductPaths.extensionWord_nonabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:57.737755+00:00
-- url     : https://prove2.me/submissions/56d9a86c-cebb-46b6-8c03-ad022d0c73c9

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_extendWord_nonabelian

set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) (n : ℕ) :
    Nonabelian f (extensionWord f w n) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      change Nonabelian f ((extendWord f)^[n + 1] w)
      rw [Function.iterate_succ_apply']
      exact extendWord_nonabelian f hf _ ih
end Kourovka.ProductPaths
