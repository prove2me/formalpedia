-- Prove2me | Theorems.Thm_Kourovka_CenterWeight_quotient_nontrivial
-- name    : Kourovka.CenterWeight.quotient_nontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:23.757648+00:00
-- url     : https://prove2.me/theorems/6363dc1a-b1c4-45e8-a3f7-83cf8b667848
-- title:
--   Center Weight: quotient nontrivial
-- statement:
--   The Center Weight construction uses the quotient nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L30-L37
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/CenterWeight.lean#L30-L37

import Definitions.Def_Kourovka_SolvableWeight
import Definitions.Def_Kourovka_CentralProducts
import Definitions.Def_Kourovka_CenterWeight
set_option autoImplicit true
open Kourovka
open Kourovka.CenterWeight
variable {G H : Type*} [Group G] [Group H]

theorem Kourovka.CenterWeight.quotient_nontrivial (h : ∃ x y : G, ¬ Commute x y) :
    Nontrivial (G ⧸ Subgroup.center G) := by sorry
