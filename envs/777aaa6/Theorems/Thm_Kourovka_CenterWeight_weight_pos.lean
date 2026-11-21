-- Prove2me | Theorems.Thm_Kourovka_CenterWeight_weight_pos
-- name    : Kourovka.CenterWeight.weight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:39:44.080422+00:00
-- url     : https://prove2.me/theorems/873b03dd-6d6f-4119-8def-8be06eb0fb6a
-- title:
--   Center Weight: weight pos
-- statement:
--   The Center Weight construction uses the weight pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L39-L42
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L39-L42

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_pos
import Theorems.Thm_Kourovka_SolvableWeight_weight_pos

set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]

theorem Kourovka.CenterWeight.weight_pos [Group.FG G] [IsSolvable G]
    (h : ∃ x y : G, ¬ Commute x y) : 0 < weight G := by sorry
