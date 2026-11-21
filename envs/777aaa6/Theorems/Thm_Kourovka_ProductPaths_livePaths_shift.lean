-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_livePaths_shift
-- name    : Kourovka.ProductPaths.livePaths_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:22.116182+00:00
-- url     : https://prove2.me/theorems/26d58fd0-8482-44f1-badc-4f1f78a1992a
-- title:
--   Product Paths: live Paths shift
-- statement:
--   Deleting the first vertex preserves an infinite nonabelian path.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L116-L121
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L116-L121

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.livePaths_shift (f : A × B →* A × B) (x : ℕ → Bool) (hx : x ∈ livePaths f) :
    FinitePaths.shift x ∈ livePaths f := by sorry
