-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_path_central_of_not_nonabelian
-- name    : Kourovka.ProductPaths.path_central_of_not_nonabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:58.596636+00:00
-- url     : https://prove2.me/theorems/92be6bc6-be2c-4c4c-a3ba-f4f50d0d3525
-- title:
--   Product Paths: path central of not nonabelian
-- statement:
--   Every abelian path image is central in the whole product.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExpansion.lean#L51-L65
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExpansion.lean#L51-L65

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.path_central_of_not_nonabelian (f : A × B →* A × B)
    (hf : Function.Surjective f) (w : List Bool) (hn : ¬ Nonabelian f w) (x : A × B) :
    path f w x ∈ Subgroup.center (A × B) := by sorry
