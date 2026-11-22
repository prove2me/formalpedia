-- Prove2me | Theorems.Thm_computation_is_linearisation
-- name    : computation_is_linearisation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:00:53.26628+00:00
-- url     : https://prove2.me/theorems/c7ea1120-fe12-4d91-b4d1-37b7b6c0cb0e
-- title:
--   computation is linearisation: computation is linearisation
-- statement:
--   Every computation determines a linearisation of its target configuration.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Computation.lean#L26-L29
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Computation.lean#L26-L29

import Definitions.Def_EventStructures_Family_Path
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.Logic.Function.Basic
import Definitions.Def_EventStructures_Family_Computation
set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily Path Trace

theorem computation_is_linearisation {c : Conf F} (comp : Computation F c) :
    ∃ t : List F.Event, isLinearisation F c t := by sorry
