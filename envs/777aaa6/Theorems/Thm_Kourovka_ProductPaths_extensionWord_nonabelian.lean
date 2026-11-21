-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_extensionWord_nonabelian
-- name    : Kourovka.ProductPaths.extensionWord_nonabelian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:32.314211+00:00
-- url     : https://prove2.me/theorems/9fba5cde-af3e-44bc-a4e5-3da9795014e8
-- title:
--   Product Paths: extension Word nonabelian
-- statement:
--   The Product Paths construction uses the extension Word nonabelian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L47-L55
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L47-L55

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.extensionWord_nonabelian (f : A × B →* A × B) (hf : Function.Surjective f)
    (w : List Bool) (h : Nonabelian f w) (n : ℕ) :
    Nonabelian f (extensionWord f w n) := by sorry
