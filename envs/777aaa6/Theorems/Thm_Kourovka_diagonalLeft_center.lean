-- Prove2me | Theorems.Thm_Kourovka_diagonalLeft_center
-- name    : Kourovka.diagonalLeft_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:35:58.433879+00:00
-- url     : https://prove2.me/theorems/49b4fd5a-49a8-4697-bc52-db16c6d5894a
-- title:
--   Kourovka: diagonal Left center
-- statement:
--   The Kourovka construction uses the diagonal Left center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L13-L15
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L13-L15

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.diagonalLeft_center (f : A × B →* A × B) (hf : Function.Surjective f)
    {z : A} (hz : z ∈ Subgroup.center A) : diagonalLeft f z ∈ Subgroup.center A := by sorry
