-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_coordinate_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.coordinate_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:22.15697+00:00
-- url     : https://prove2.me/theorems/554d9a73-598a-4b6b-84a7-c242ce1ccf2e
-- title:
--   Computable Cone: coordinate primrec
-- statement:
--   The Computable Cone construction uses the coordinate primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L216-L221
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L216-L221

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.coordinate_primrec : Primrec (fun p : (ℕ × ℕ) × (ℤ × ℤ) =>
    coordinate p.1.1 p.1.2 p.2.1 p.2.2) := by sorry
