-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_finitePath_middle_eq_terminal
-- name    : Kourovka.ProductPaths.finitePath_middle_eq_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:40:18.648825+00:00
-- url     : https://prove2.me/theorems/d444ae01-fbf0-4f65-b6dd-41fa6ca436f8
-- title:
--   Product Paths: finite Path middle eq terminal
-- statement:
--   The common shift identity applies to every sufficiently long finite nonabelian path.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L124-L130
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L124-L130

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.finitePath_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw := by sorry
