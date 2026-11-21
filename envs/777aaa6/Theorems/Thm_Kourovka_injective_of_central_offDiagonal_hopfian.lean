-- Prove2me | Theorems.Thm_Kourovka_injective_of_central_offDiagonal_hopfian
-- name    : Kourovka.injective_of_central_offDiagonal_hopfian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:31.895178+00:00
-- url     : https://prove2.me/theorems/2c79401d-d240-4a51-982b-3b3e9a5c3d7f
-- title:
--   Kourovka: injective of central off Diagonal hopfian
-- statement:
--   Central mixing cannot destroy Hopficity of finitely generated factors.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L49-L70
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L49-L70

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.injective_of_central_offDiagonal_hopfian [Group.FG A] [Group.FG B]
    (hA : IsHopfian A) (hB : IsHopfian B)
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) : Function.Injective f := by sorry
