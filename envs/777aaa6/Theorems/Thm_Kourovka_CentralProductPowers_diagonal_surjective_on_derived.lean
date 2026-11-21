-- Prove2me | Theorems.Thm_Kourovka_CentralProductPowers_diagonal_surjective_on_derived
-- name    : Kourovka.CentralProductPowers.diagonal_surjective_on_derived
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:04.915338+00:00
-- url     : https://prove2.me/theorems/9a8782aa-c79c-431d-9170-326b9cab3dfe
-- title:
--   Central Product Powers: diagonal surjective on derived
-- statement:
--   A surjective product map with central off-diagonal entries maps each derived
--   factor onto itself through its diagonal entry.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralProductPowers.lean#L48-L84
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralProductPowers.lean#L48-L84

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_CentralProductPowers
set_option autoImplicit true
open Kourovka Kourovka.CentralProductPowers
open ProductPaths
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.CentralProductPowers.diagonal_surjective_on_derived (f : A × B →* A × B)
    (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) :
    (∀ y ∈ commutator A, ∃ x ∈ commutator A, (f (x, 1)).1 = y) ∧
    (∀ y ∈ commutator B, ∃ x ∈ commutator B, (f (1, x)).2 = y) := by sorry
