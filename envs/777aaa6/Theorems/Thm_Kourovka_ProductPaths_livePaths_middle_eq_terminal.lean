-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_livePaths_middle_eq_terminal
-- name    : Kourovka.ProductPaths.livePaths_middle_eq_terminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:39:56.413902+00:00
-- url     : https://prove2.me/theorems/3b59da00-b279-495c-a7f6-cd84f3160c0e
-- title:
--   Product Paths: live Paths middle eq terminal
-- statement:
--   One common power of the shift agrees with its square on every live path.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L136-L141
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L136-L141

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.livePaths_middle_eq_terminal [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ livePaths f, x m = x (2 * m) := by sorry
