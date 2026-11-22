-- Prove2me | Theorems.Thm_execList_exists
-- name    : execList_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:01:01.592804+00:00
-- url     : https://prove2.me/theorems/91f5e0fa-a897-4d8c-b5b2-ac0c59337d43
-- title:
--   exec List exists: exec List exists
-- statement:
--   The same, as an execution list.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Reachability.lean#L54-L58
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Reachability.lean#L54-L58

import Definitions.Def_EventStructures_Family_Path
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Family_Reachability
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)

theorem execList_exists {c₀ c : Conf F} (hsub : c₀.val ⊆ c.val)
    (hfin : (c.val \ c₀.val).Finite) :
    Nonempty (Σ t : List F.Event, Path.ExecList F c₀ t c) := by sorry
