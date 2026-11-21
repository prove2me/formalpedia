-- Prove2me | Theorems.Thm_Kourovka_SolvableWeight_weight_add_le
-- name    : Kourovka.SolvableWeight.weight_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:57.994076+00:00
-- url     : https://prove2.me/theorems/5483f1ae-c1e9-4350-b9f0-1757436ef67f
-- title:
--   Solvable Weight: weight add le
-- statement:
--   Direct factors consume at least their own positive measure.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L74-L83
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L74-L83

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_add_le

set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]

theorem Kourovka.SolvableWeight.weight_add_le [Group.FG G] [Group.FG H] :
    weight G + weight H ≤ weight (G × H) := by sorry
