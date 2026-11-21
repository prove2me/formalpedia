-- Prove2me | Theorems.Thm_Kourovka_SolvableWeight_weight_pos
-- name    : Kourovka.SolvableWeight.weight_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:30:21.302707+00:00
-- url     : https://prove2.me/theorems/4802661c-b2ad-4df2-bb37-088f3341ead3
-- title:
--   Solvable Weight: weight pos
-- statement:
--   The Solvable Weight construction uses the weight pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L69-L71
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L69-L71

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_pos

set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]

theorem Kourovka.SolvableWeight.weight_pos [Group.FG G] [IsSolvable G] [Nontrivial G] : 0 < weight G := by sorry
