-- Prove2me | Theorems.Thm_reach_append
-- name    : reach_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:46.457322+00:00
-- url     : https://prove2.me/theorems/84e4d12c-4af5-4425-8160-6292d6bfa18c
-- title:
--   reach append: reach append
-- statement:
--   Running `t` and then `p` is running `t ++ p`.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L138-L140
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Trace.lean#L138-L140

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Algebra.Group.Defs
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic
import Definitions.Def_EventStructures_Family_Trace
set_option autoImplicit true
variable {α L : Type*} (R : α → α → Prop) (lbl : α → L)
local infixr:60 " ≈ₜ " => TraceEquiv R

theorem reach_append {L : Type*} (F : ConfFamily L) (c : Set F.Event) (t p : List F.Event) :
    reach F (reach F c t) p = reach F c (t ++ p) := by sorry
