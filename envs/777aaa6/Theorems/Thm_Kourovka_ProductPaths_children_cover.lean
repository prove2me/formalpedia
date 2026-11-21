-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_children_cover
-- name    : Kourovka.ProductPaths.children_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:38.507812+00:00
-- url     : https://prove2.me/theorems/4cc80de4-4aa4-4cd2-b5d0-7b2bacf7d174
-- title:
--   Product Paths: children cover
-- statement:
--   The two child images multiply onto the parent image.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Paths.lean#L73-L79
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/Paths.lean#L73-L79

import Definitions.Def_Kourovka_Components
import Mathlib.Data.List.Basic
import Definitions.Def_Kourovka_Paths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.children_cover (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (x : A × B) :
    ∃ y z, path f (w ++ [false]) y * path f (w ++ [true]) z = path f w x := by sorry
