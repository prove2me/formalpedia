-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_checkNat_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.checkNat_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:20.012181+00:00
-- url     : https://prove2.me/theorems/afc1dcdd-e61e-4a79-af97-907d0d5a32fc
-- title:
--   Computable Closure: check Nat primrec
-- statement:
--   The Computable Closure construction uses the check Nat primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L173-L175
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L173-L175

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv

theorem Kourovka.MetabelianEnumeration.ComputableClosure.checkNat_primrec : Primrec₂ (@checkNat G _ _ _) := by sorry
