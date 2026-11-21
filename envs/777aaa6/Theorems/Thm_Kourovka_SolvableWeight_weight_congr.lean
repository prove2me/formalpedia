-- Prove2me | Theorems.Thm_Kourovka_SolvableWeight_weight_congr
-- name    : Kourovka.SolvableWeight.weight_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:54.658933+00:00
-- url     : https://prove2.me/theorems/af69ebba-964d-4645-b2bc-3a17b4ac52bc
-- title:
--   Solvable Weight: weight congr
-- statement:
--   The Solvable Weight construction uses the weight congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L66-L67
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L66-L67

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
import Theorems.Thm_Kourovka_AbelianWeight_weight_congr

set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]

theorem Kourovka.SolvableWeight.weight_congr (e : G ≃* H) : weight G = weight H := by sorry
