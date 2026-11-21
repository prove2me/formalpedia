-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_extendWord_nonabelian
-- name    : Kourovka.ProductPaths.extendWord_nonabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:30.036214+00:00
-- url     : https://prove2.me/theorems/8b376e6e-42f8-4025-ae46-8eaa047cce92
-- title:
--   Product Paths: extend Word nonabelian
-- statement:
--   The Product Paths construction uses the extend Word nonabelian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L26-L32
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L26-L32

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.extendWord_nonabelian (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) : Nonabelian f (extendWord f w) := by sorry
