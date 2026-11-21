-- Prove2me | Theorems.Thm_Kourovka_ProductPaths_factorial_mixed_iterate_central
-- name    : Kourovka.ProductPaths.factorial_mixed_iterate_central
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:23.810355+00:00
-- url     : https://prove2.me/theorems/ee848fd6-b89a-4a7a-9355-9056764e3916
-- title:
--   Product Paths: factorial mixed iterate central
-- statement:
--   The uniform factorial iterate kills every mixed composite modulo the center.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/MixedPaths.lean#L53-L78
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/MixedPaths.lean#L53-L78

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_MixedPaths
set_option autoImplicit true
open Kourovka
open Kourovka.ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.ProductPaths.factorial_mixed_iterate_central [Group.FG A] [Group.FG B]
    [IsSolvable A] [IsSolvable B] (f : A × B →* A × B)
    (hf : Function.Surjective f) :
    let m := (CenterWeight.weight (A × B)).factorial
    ∀ (j k : Bool), j ≠ k → ∀ x : A × B,
      f^[m] (axis j (f^[m] (axis k x))) ∈ Subgroup.center (A × B) := by sorry
