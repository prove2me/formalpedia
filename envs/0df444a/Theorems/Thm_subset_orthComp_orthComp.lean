-- Prove2me | Theorems.Thm_subset_orthComp_orthComp
-- name    : subset_orthComp_orthComp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:43.379176+00:00
-- url     : https://prove2.me/theorems/6c6af9d6-d415-4ff6-b53d-7b5023a787b4
-- title:
--   subset orth Comp orth Comp: subset orth Comp orth Comp
-- statement:
--   The subset orth Comp orth Comp construction uses the subset orth Comp orth Comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L114-L115
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L114-L115

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]

theorem subset_orthComp_orthComp (X : Set O) : X ⊆ orthComp (orthComp X) := by sorry
