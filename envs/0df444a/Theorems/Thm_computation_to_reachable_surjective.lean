-- Prove2me | Theorems.Thm_computation_to_reachable_surjective
-- name    : computation_to_reachable_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:00:55.856211+00:00
-- url     : https://prove2.me/theorems/0c8c1584-6b96-4561-8de7-529e7ed1626d
-- title:
--   computation to reachable surjective: computation to reachable surjective
-- statement:
--   The map from computations to reachable configurations is surjective.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Computation.lean#L39-L41
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Computation.lean#L39-L41

import Definitions.Def_EventStructures_Family_Path
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.Logic.Function.Basic
import Definitions.Def_EventStructures_Family_Computation
set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily Path Trace

theorem computation_to_reachable_surjective :
    Function.Surjective (computation_to_reachable F) := by sorry
