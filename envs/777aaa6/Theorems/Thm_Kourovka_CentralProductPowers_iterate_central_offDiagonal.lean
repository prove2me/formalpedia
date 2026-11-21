-- Prove2me | Theorems.Thm_Kourovka_CentralProductPowers_iterate_central_offDiagonal
-- name    : Kourovka.CentralProductPowers.iterate_central_offDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:31.303162+00:00
-- url     : https://prove2.me/theorems/f5b07465-1a28-4a33-9733-b513f918aac6
-- title:
--   Central Product Powers: iterate central off Diagonal
-- statement:
--   Central off-diagonal entries remain central under every iterate.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralProductPowers.lean#L15-L44
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralProductPowers.lean#L15-L44

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_CentralProductPowers
set_option autoImplicit true
open Kourovka Kourovka.CentralProductPowers
open ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.CentralProductPowers.iterate_central_offDiagonal (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) (n : ℕ) :
    (∀ b, (iterateHom f n (1, b)).1 ∈ Subgroup.center A) ∧
    (∀ a, (iterateHom f n (a, 1)).2 ∈ Subgroup.center B) := by sorry
