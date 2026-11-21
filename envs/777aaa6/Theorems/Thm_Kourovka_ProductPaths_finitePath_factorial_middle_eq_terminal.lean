-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_finitePath_factorial_middle_eq_terminal
-- name    : Kourovka.ProductPaths.finitePath_factorial_middle_eq_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:27.113264+00:00
-- url     : https://prove2.me/theorems/665112ba-3271-44b1-99e6-2521d35ca5d8
-- title:
--   Product Paths: finite Path factorial middle eq terminal
-- statement:
--   The uniform factorial shift identity holds on all sufficiently long nonabelian paths.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L105-L121
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/PathExtension.lean#L105-L121

import Definitions.Def_Kourovka_LivePaths
import Mathlib.Data.List.Infix
import Definitions.Def_Kourovka_PathExtension
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.finitePath_factorial_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∀ (w : List Bool) (hw : 2 * m < w.length), Nonabelian f w →
      w[m]'(by omega) = w[2 * m]'hw := by sorry
