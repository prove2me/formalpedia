-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_nonabelian_child
-- name    : Kourovka.ProductPaths.nonabelian_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:46.680148+00:00
-- url     : https://prove2.me/theorems/2c40f21b-7dc4-4cfa-9fde-77754e0c7a99
-- title:
--   Product Paths: nonabelian child
-- statement:
--   A nonabelian path has a nonabelian right extension.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Paths.lean#L99-L118
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Paths.lean#L99-L118

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.nonabelian_child (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) :
    Nonabelian f (w ++ [false]) ∨ Nonabelian f (w ++ [true]) := by sorry
