-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_check_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.check_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:42:34.690722+00:00
-- url     : https://prove2.me/theorems/e01a8851-4dda-4b1a-81ec-10cb14a47239
-- title:
--   Computable Closure: check correct
-- statement:
--   The Computable Closure construction uses the check correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L164-L168
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L164-L168

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit hmul hinv [Primcodable G]

theorem Kourovka.MetabelianEnumeration.ComputableClosure.check_correct (input : List G × G) :
    (∃ certificate, check input certificate = true) ↔
      input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1} := by sorry
