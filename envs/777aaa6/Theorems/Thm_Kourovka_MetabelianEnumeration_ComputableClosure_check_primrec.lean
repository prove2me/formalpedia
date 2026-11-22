-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.check_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:31.009334+00:00
-- url     : https://prove2.me/theorems/23f43e00-7079-4ee5-9a64-c1529d53d4cd
-- title:
--   Computable Closure: check primrec
-- statement:
--   The Computable Closure construction uses the check primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L155-L161
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L155-L161

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv

theorem Kourovka.MetabelianEnumeration.ComputableClosure.check_primrec : Primrec₂ (@check G _ _) := by sorry
