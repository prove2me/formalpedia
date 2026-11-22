-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_normalClosure_re
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.normalClosure_re
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:51:19.449163+00:00
-- url     : https://prove2.me/theorems/c6fca920-23ad-496f-8d01-f89d31cf9345
-- title:
--   Computable Closure: normal Closure re
-- statement:
--   The Computable Closure construction uses the normal Closure re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L189-L197
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L189-L197

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]
variable [Primcodable G] [DecidableEq G]
variable (hmul : Primrec₂ (fun x y : G => x * y)) (hinv : Primrec (fun x : G => x⁻¹))
include hmul hinv

theorem Kourovka.MetabelianEnumeration.ComputableClosure.normalClosure_re :
    REPred (fun input : List G × G => input.2 ∈ Subgroup.normalClosure {r | r ∈ input.1}) := by sorry
