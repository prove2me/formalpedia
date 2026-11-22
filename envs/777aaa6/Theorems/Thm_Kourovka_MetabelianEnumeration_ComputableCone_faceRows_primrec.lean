-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_faceRows_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.faceRows_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:33.635313+00:00
-- url     : https://prove2.me/theorems/4a66c05b-410e-4742-8d5e-8c04d7cfab57
-- title:
--   Computable Cone: face Rows primrec
-- statement:
--   The Computable Cone construction uses the face Rows primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L231-L237
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L231-L237

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.faceRows_primrec : Primrec (fun p : (ℕ × ℕ) × ℤ => faceRows p.1.1 p.1.2 p.2) := by sorry
