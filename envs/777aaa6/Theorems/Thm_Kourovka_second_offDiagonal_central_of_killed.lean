-- Prove2me | Theorems.Thm_Kourovka_second_offDiagonal_central_of_killed
-- name    : Kourovka.second_offDiagonal_central_of_killed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:56.137397+00:00
-- url     : https://prove2.me/theorems/8b6af873-4d47-46ed-8d3f-225dc06b1ae2
-- title:
--   Kourovka: second off Diagonal central of killed
-- statement:
--   The symmetric off-diagonal image satisfies the same conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L70-L80
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/EventualCentrality.lean#L70-L80

import Definitions.Def_Kourovka_MixedPaths
import Definitions.Def_Kourovka_CenterQuotients
import Definitions.Def_Kourovka_EventualCentrality
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.second_offDiagonal_central_of_killed [Group.FG A] [Group.FG B] [IsSolvable B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (hk : ∀ a : A, f (1, (f (a, 1)).2) ∈ Subgroup.center (A × B)) :
    ∀ a : A, (f (a, 1)).2 ∈ Subgroup.center B := by sorry
