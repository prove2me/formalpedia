-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_checkNat_correct
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.checkNat_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:46:20.846848+00:00
-- url     : https://prove2.me/theorems/09979153-4226-4054-8713-02a5fac00059
-- title:
--   Computable Closure: check Nat correct
-- statement:
--   The Computable Closure construction uses the check Nat correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L178-L187
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L178-L187

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv
omit hmul hinv

theorem Kourovka.MetabelianEnumeration.ComputableClosure.checkNat_correct (input : List G × G) :
    (∃ certificate, checkNat input certificate = true) ↔
      input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1} := by sorry
