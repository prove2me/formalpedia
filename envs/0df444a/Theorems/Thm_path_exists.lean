-- Prove2me | Theorems.Thm_path_exists
-- name    : path_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:53:13.986175+00:00
-- url     : https://prove2.me/theorems/3ebf4b16-f51a-4b02-87ba-500563ef0d06
-- title:
--   path exists: path exists
-- statement:
--   A configuration is reachable from any subconfiguration with a finite gap.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Reachability.lean#L49-L51
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Reachability.lean#L49-L51

import Definitions.Def_EventStructures_Family_Path
import Mathlib.Data.Set.Card
import Definitions.Def_EventStructures_Family_Reachability
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)

theorem path_exists {c₀ c : Conf F} (hsub : c₀.val ⊆ c.val)
    (hfin : (c.val \ c₀.val).Finite) : Nonempty (Path F c₀ c) := by sorry
