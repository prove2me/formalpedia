-- Prove2me | Theorems.Thm_Kourovka_directProduct_isHopfian
-- name    : Kourovka.directProduct_isHopfian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:34.115309+00:00
-- url     : https://prove2.me/theorems/952893f6-a17a-496e-89da-cef6b473db72
-- title:
--   Kourovka: direct Product is Hopfian
-- statement:
--   The direct product of two finitely generated soluble Hopfian groups is Hopfian.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L73-L79
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L73-L79

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.directProduct_isHopfian [Group.FG A] [Group.FG B] [IsSolvable A] [IsSolvable B]
    (hA : IsHopfian A) (hB : IsHopfian B) : IsHopfian (A × B) := by sorry
