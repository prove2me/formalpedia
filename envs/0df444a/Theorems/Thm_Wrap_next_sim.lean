-- Prove2me | Theorems.Thm_Wrap_next_sim
-- name    : Wrap.next_sim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:44:04.940121+00:00
-- url     : https://prove2.me/theorems/d9c6771a-6a34-4b8c-a6b6-6416acc3b217
-- title:
--   Wrap: next sim
-- statement:
--   One step of the iteration of the simulation, on the value for the configuration c, gives the
--   value for the next configuration of M; a halted configuration stays as it is on both sides.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L72-L77
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L72-L77

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

theorem Wrap.next_sim (K : Coding M) (pre post : List Bool → List Bool) (c : M.tm.Cfg) :
    (sim K pre post).next (K.rep c) = K.rep (stay M c) := by sorry
