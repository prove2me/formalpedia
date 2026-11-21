-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_axis_path
-- name    : Kourovka.ProductPaths.axis_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:44.031591+00:00
-- url     : https://prove2.me/theorems/f1a6e0d7-c666-4cd8-abbb-98f34c8b033a
-- title:
--   Product Paths: axis path
-- statement:
--   A projected path vanishes unless its first vertex is the selected factor.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExpansion.lean#L86-L91
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExpansion.lean#L86-L91

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.axis_path (i j : Bool) (f : A × B →* A × B) (w : List Bool) (x : A × B) :
    axis i (path f (j :: w) x) = if i = j then path f (j :: w) x else 1 := by sorry
