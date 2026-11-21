-- Prove2me | Theorems.Thm_Kourovka_SolvableWeight_abelianization_nontrivial
-- name    : Kourovka.SolvableWeight.abelianization_nontrivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:18.029992+00:00
-- url     : https://prove2.me/theorems/71737fe1-25c8-422f-b136-216fe822b475
-- title:
--   Solvable Weight: abelianization nontrivial
-- statement:
--   A nontrivial soluble group has nontrivial abelianization.
--
--   Source: https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L51-L61
-- source:
--   https://github.com/Achxy/k-5-38/blob/4330f0513173258259f0585d1c1b8a624fda59d2/Kourovka/SolvableWeight.lean#L51-L61

import Definitions.Def_Kourovka_AbelianWeight
import Mathlib.Algebra.Group.Equiv.TypeTags
import Definitions.Def_Kourovka_SolvableWeight
set_option autoImplicit true
open Kourovka
open Kourovka.SolvableWeight
variable (G H : Type*) [Group G] [Group H]

theorem Kourovka.SolvableWeight.abelianization_nontrivial [IsSolvable G] [Nontrivial G] :
    Nontrivial (Abelianization G) := by sorry
