-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_expand_primrec
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.expand_primrec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:55.247153+00:00
-- url     : https://prove2.me/theorems/e41268c7-4615-4b07-a922-caf6a61d990f
-- title:
--   Computable Closure: expand primrec
-- statement:
--   The Computable Closure construction uses the expand primrec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L128-L143
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L128-L143

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit [DecidableEq G]

theorem Kourovka.MetabelianEnumeration.ComputableClosure.expand_primrec : Primrec₂ (@expand G _) := by sorry
