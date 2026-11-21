-- Prove2me | Theorems.Thm_orthComp_orthComp_orthComp
-- name    : orthComp_orthComp_orthComp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:17.29914+00:00
-- url     : https://prove2.me/theorems/29546e5d-4652-42ac-8c4c-b8626d818f54
-- title:
--   orth Comp orth Comp orth Comp: orth Comp orth Comp orth Comp
-- statement:
--   The orth Comp orth Comp orth Comp construction uses the orth Comp orth Comp orth Comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L117-L121
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L117-L121

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]

theorem orthComp_orthComp_orthComp (X : Set O) :
    orthComp (orthComp (orthComp X)) = orthComp X := by sorry
