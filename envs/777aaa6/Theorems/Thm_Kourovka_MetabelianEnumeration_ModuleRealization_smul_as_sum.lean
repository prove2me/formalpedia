-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_smul_as_sum
-- name    : Kourovka.MetabelianEnumeration.ModuleRealization.smul_as_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:41.278104+00:00
-- url     : https://prove2.me/theorems/5a607909-b1cc-412b-bd4a-d3bb26b01fff
-- title:
--   Module Realization: smul as sum
-- statement:
--   The Module Realization construction uses the smul as sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L53-L62
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L53-L62

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.ModuleRealization.smul_as_sum (p : GroupRing (Lattice k)) (m : M) :
    p • m = (p.support.toList.map fun u => p u •
      ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)).sum := by sorry
