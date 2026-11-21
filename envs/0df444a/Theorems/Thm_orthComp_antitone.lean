-- Prove2me | Theorems.Thm_orthComp_antitone
-- name    : orthComp_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:06:32.03719+00:00
-- url     : https://prove2.me/theorems/beb90a94-5b43-4b72-b994-31301d34f8d1
-- title:
--   orth Comp antitone: orth Comp antitone
-- statement:
--   The orth Comp antitone construction uses the orth Comp antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L111-L112
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L111-L112

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]

theorem orthComp_antitone {X Y : Set O} (h : X ⊆ Y) : orthComp Y ⊆ orthComp X := by sorry
