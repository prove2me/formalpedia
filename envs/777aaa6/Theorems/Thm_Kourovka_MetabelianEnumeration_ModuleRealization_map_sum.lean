-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_map_sum
-- name    : Kourovka.MetabelianEnumeration.ModuleRealization.map_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:09.598734+00:00
-- url     : https://prove2.me/theorems/f8513a43-5098-4c79-8a6f-60a18176927d
-- title:
--   Module Realization: map sum
-- statement:
--   The Module Realization construction uses the map sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L38-L42
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L38-L42

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.ModuleRealization.map_sum (j : Multiplicative M →* G) (xs : List M) :
    j (Multiplicative.ofAdd xs.sum) = (xs.map fun m => j (Multiplicative.ofAdd m)).prod := by sorry
