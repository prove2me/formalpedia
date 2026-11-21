-- Prove2me | Theorems.Thm_Kourovka_CenterWeight_weight_congr
-- name    : Kourovka.CenterWeight.weight_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:32.800852+00:00
-- url     : https://prove2.me/theorems/12a0e32a-cdf6-4fca-badd-78f62cabc54f
-- title:
--   Center Weight: weight congr
-- statement:
--   The Center Weight construction uses the weight congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L27-L28
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L27-L28

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr
import Theorems.Thm_Kourovka_SolvableWeight_weight_congr

set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]

theorem Kourovka.CenterWeight.weight_congr (e : G ≃* H) : weight G = weight H := by sorry
