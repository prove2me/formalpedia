-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_livePaths_factorial_middle_eq_terminal
-- name    : Kourovka.ProductPaths.livePaths_factorial_middle_eq_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:38.296173+00:00
-- url     : https://prove2.me/theorems/abbc4d39-6e1b-4fc3-b153-289c7d2ae138
-- title:
--   Product Paths: live Paths factorial middle eq terminal
-- statement:
--   The factorial of the product's weight works for every live path and every epimorphism.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L124-L133
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L124-L133

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.livePaths_factorial_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∀ x ∈ livePaths f,
      x (CenterWeight.weight (A × B)).factorial =
        x (2 * (CenterWeight.weight (A × B)).factorial) := by sorry
