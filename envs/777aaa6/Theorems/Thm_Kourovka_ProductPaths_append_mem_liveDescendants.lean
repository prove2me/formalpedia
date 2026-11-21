-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_append_mem_liveDescendants
-- name    : Kourovka.ProductPaths.append_mem_liveDescendants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:33:18.931796+00:00
-- url     : https://prove2.me/theorems/1795033f-1abf-459f-a910-b09664c7d856
-- title:
--   Product Paths: append mem live Descendants
-- statement:
--   Every nonabelian extension occurs in the corresponding finite level.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L30-L42
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/LivePaths.lean#L30-L42

import Definitions.Def_Kourovka_PathWeight
import Definitions.Def_Kourovka_FinitePaths
import Mathlib.Data.List.OfFn
import Definitions.Def_Kourovka_LivePaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.append_mem_liveDescendants (f : A × B →* A × B) (u : List Bool) :
    ∀ w, Nonabelian f (w ++ u) → w ++ u ∈ liveDescendants f w u.length := by sorry
