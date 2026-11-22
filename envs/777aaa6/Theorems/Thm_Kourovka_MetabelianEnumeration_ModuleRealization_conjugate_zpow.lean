-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_conjugate_zpow
-- name    : Kourovka.MetabelianEnumeration.ModuleRealization.conjugate_zpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:16.64119+00:00
-- url     : https://prove2.me/theorems/69d01b2b-1309-48e6-be52-08f2710c7edd
-- title:
--   Module Realization: conjugate zpow
-- statement:
--   The Module Realization construction uses the conjugate zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L77-L78
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L77-L78

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.ModuleRealization.conjugate_zpow (x w : G) (c : ℤ) : conjugate (x ^ c) w = (conjugate x w) ^ c := by sorry
