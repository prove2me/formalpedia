-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_mem_normalClosure_iff
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.mem_normalClosure_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:53.511693+00:00
-- url     : https://prove2.me/theorems/31ccd02c-0e52-4328-96b3-c7ac13fa08b4
-- title:
--   Computable Closure: mem normal Closure iff
-- statement:
--   The Computable Closure construction uses the mem normal Closure iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L111-L118
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L111-L118

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.ComputableClosure.mem_normalClosure_iff (rels : List G) (x : G) :
    x ∈ Subgroup.normalClosure {r | r ∈ rels} ↔ ∃ C n, x ∈ stages rels C n := by sorry
