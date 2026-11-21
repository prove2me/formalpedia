-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_livePaths_finite
-- name    : Kourovka.ProductPaths.livePaths_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:39:37.330023+00:00
-- url     : https://prove2.me/theorems/5ebe78e4-78da-4dd5-966e-22ddae998a3a
-- title:
--   Product Paths: live Paths finite
-- statement:
--   There are only finitely many infinite nonabelian paths.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L104-L108
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L104-L108

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.livePaths_finite [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) : (livePaths f).Finite := by sorry
