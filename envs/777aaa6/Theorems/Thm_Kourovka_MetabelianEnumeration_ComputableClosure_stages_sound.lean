-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ComputableClosure_stages_sound
-- name    : Kourovka.MetabelianEnumeration.ComputableClosure.stages_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:50:56.868772+00:00
-- url     : https://prove2.me/theorems/597f400c-6f47-4874-acb8-b4ab11cb22ac
-- title:
--   Computable Closure: stages sound
-- statement:
--   The Computable Closure construction uses the stages sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L66-L80
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Computability/ComputableClosure.lean#L66-L80

import Definitions.Def_Kourovka_Computability_ComputableWords
import Definitions.Def_Kourovka_Computability_ComputableClosure
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ComputableClosure
variable {G : Type*} [Group G]

theorem Kourovka.MetabelianEnumeration.ComputableClosure.stages_sound (rels C : List G) (n : ℕ) {x : G}
    (hx : x ∈ stages rels C n) : x ∈ Subgroup.normalClosure {r | r ∈ rels} := by sorry
