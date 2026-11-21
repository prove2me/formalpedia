-- Prove2me | Theorems.Thm_Kourovka_diagonalRight_center
-- name    : Kourovka.diagonalRight_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:36:06.910859+00:00
-- url     : https://prove2.me/theorems/0e76a38b-d01a-4203-b002-d1d8b410bfe6
-- title:
--   Kourovka: diagonal Right center
-- statement:
--   The Kourovka construction uses the diagonal Right center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L17-L19
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CentralHopfian.lean#L17-L19

import Definitions.Def_Kourovka_DiagonalCongruence
import Definitions.Def_Kourovka_CentralProductPowers
import Definitions.Def_Kourovka_EventualCentrality
import Definitions.Def_Kourovka_CentralHopfian
set_option autoImplicit true
open Kourovka
variable {A B : Type*} [Group A] [Group B]

theorem Kourovka.diagonalRight_center (f : A × B →* A × B) (hf : Function.Surjective f)
    {z : B} (hz : z ∈ Subgroup.center B) : diagonalRight f z ∈ Subgroup.center B := by sorry
