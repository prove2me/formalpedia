-- Prove2me | Theorems.Thm_Wrap_size_rep_iterate_le
-- name    : Wrap.size_rep_iterate_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:44:29.535519+00:00
-- url     : https://prove2.me/theorems/76d35541-6503-41dd-aab9-e2c280973e47
-- title:
--   Wrap: size rep iterate le
-- statement:
--   j steps of M add at most j times the constant of the coding to the size of the value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L90-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L90-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_Wrap_Sim
set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}

theorem Wrap.size_rep_iterate_le (K : Coding M) (c : M.tm.Cfg) (j : ℕ) : size (K.rep ((stay M)^[j] c)) ≤ size (K.rep c) + K.a * j := by sorry
