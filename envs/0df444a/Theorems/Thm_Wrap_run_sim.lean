-- Prove2me | Theorems.Thm_Wrap_run_sim
-- name    : Wrap.run_sim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:40.284575+00:00
-- url     : https://prove2.me/theorems/cb4a73f0-6a8b-4c43-b5a2-f9cbb95fa1ab
-- title:
--   Wrap: run sim
-- statement:
--   After j steps the state of the simulation on x is the value for the configuration of M after j
--   steps on `pre x`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L81-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L81-L87

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}

theorem Wrap.run_sim (K : Coding M) (pre post : List Bool → List Bool) (x : List Bool) (j : ℕ) :
    (sim K pre post).run x j = K.rep ((stay M)^[j] (initList M.tm ((pre x).map M.inputAlphabet.invFun))) := by sorry
