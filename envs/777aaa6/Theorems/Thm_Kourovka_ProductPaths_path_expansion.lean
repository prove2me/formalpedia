-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_path_expansion
-- name    : Kourovka.ProductPaths.path_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:56.926172+00:00
-- url     : https://prove2.me/theorems/d584800a-e174-4650-87cf-f1036d719d77
-- title:
--   Product Paths: path expansion
-- statement:
--   Expand an iterate as a product of its equal-level path homomorphisms.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExpansion.lean#L35-L48
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExpansion.lean#L35-L48

import Definitions.Def_Kourovka_PathExtension
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Definitions.Def_Kourovka_PathExpansion
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.path_expansion (f : A × B →* A × B) (n : ℕ) (x : A × B) :
    ((allWords n).map (fun w => path f w x)).prod = f^[n] x := by sorry
