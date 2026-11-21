-- Prove2me | Theorems.Thm_Kourovka_centralCorrection_injective_on_derived
-- name    : Kourovka.centralCorrection_injective_on_derived
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:43.506567+00:00
-- url     : https://prove2.me/theorems/f4e783e9-ef11-46d8-a204-82530bbb741b
-- title:
--   Kourovka: central Correction injective on derived
-- statement:
--   Once a correction is surjective, Hopficity makes the original map injective on the derived group.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L36-L43
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/DerivedReduction.lean#L36-L43

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]

theorem Kourovka.centralCorrection_injective_on_derived (hG : IsHopfian G)
    (u : G →* G) (h : G →* Subgroup.center G)
    (hsurj : Function.Surjective (centralCorrection u h)) :
    Set.InjOn u (commutator G) := by sorry
