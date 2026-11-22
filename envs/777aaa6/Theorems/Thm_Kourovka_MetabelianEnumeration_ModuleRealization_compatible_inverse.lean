-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_compatible_inverse
-- name    : Kourovka.MetabelianEnumeration.ModuleRealization.compatible_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:11.606323+00:00
-- url     : https://prove2.me/theorems/3810e9a6-dd29-4b85-914a-33a3dce36e56
-- title:
--   Module Realization: compatible inverse
-- statement:
--   The Module Realization construction uses the compatible inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L64-L75
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L64-L75

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.ModuleRealization.compatible_inverse (j : Multiplicative M →* G) (t : Fin k → G)
    (h : ActionCompatible j t) (u : Lattice k) (m : M) :
    conjugate (j (Multiplicative.ofAdd m)) ((orderedWord t (-u))⁻¹) =
      j (Multiplicative.ofAdd ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)) := by sorry
