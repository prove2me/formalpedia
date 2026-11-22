-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableCone_any_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableCone.any_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:53:12.092045+00:00
-- url     : https://prove2.me/theorems/4176fa47-2373-42e4-a486-50c5889b11f0
-- title:
--   Computable Cone: any primrec
-- statement:
--   The Computable Cone construction uses the any primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L196-L206
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ComputableCone.lean#L196-L206

import Definitions.Def_Kourovka_Polyhedral_ComputableFourierMotzkin
import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Definitions.Def_Kourovka_Polyhedral_ComputableCone
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableCone
open ComputableIntegers
open ComputableFourierMotzkin (RowCode decodeRow)

theorem Kourovka.MetabelianEnumeration.ComputableCone.any_primrec {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).any (p a)) := by sorry
