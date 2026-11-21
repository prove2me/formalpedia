-- Prove2me | solution 1 for Kourovka.ProductPaths.extendWord_nonabelian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:39:49.875337+00:00
-- url     : https://prove2.me/submissions/f0149ba1-5d41-4f40-a09f-92b413e5614c

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
import Theorems.Thm_Kourovka_ProductPaths_nonabelian_child


set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.ProductPaths
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) : Nonabelian f (extendWord f w) := by
  classical
  unfold extendWord
  split_ifs with hfalse
  · exact hfalse
  · exact (nonabelian_child f hf w h).resolve_left hfalse
end Kourovka.ProductPaths
