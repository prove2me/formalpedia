-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_polynomialSupport_encode
-- name    : Kourovka.MetabelianEnumeration.ModuleRealization.polynomialSupport_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:06.96866+00:00
-- url     : https://prove2.me/theorems/49322ec4-f095-4414-82a1-3715f709f4cc
-- title:
--   Module Realization: polynomial Support encode
-- statement:
--   The Module Realization construction uses the polynomial Support encode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L26-L32
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L26-L32

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.ModuleRealization.polynomialSupport_encode (p : SignedPolynomial k) :
    polynomialSupport (encodeSigned p) = signedSupport p := by sorry
