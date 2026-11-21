-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_mixed_iterate_central
-- name    : Kourovka.ProductPaths.mixed_iterate_central
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:41:20.837449+00:00
-- url     : https://prove2.me/theorems/7221d308-b5c3-47ce-87a0-c25fa73ea529
-- title:
--   Product Paths: mixed iterate central
-- statement:
--   A common iterate kills each mixed off-diagonal composite modulo the center.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/MixedPaths.lean#L81-L87
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/MixedPaths.lean#L81-L87

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_MixedPaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.mixed_iterate_central [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    ∃ m : ℕ, 0 < m ∧ ∀ (j k : Bool), j ≠ k → ∀ x : A × B,
      f^[m] (axis j (f^[m] (axis k x))) ∈ Subgroup.center (A × B) := by sorry
