-- Prove2me | Theorems.Thm_Wrap_sim_runs
-- name    : Wrap.sim_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:44:00.419926+00:00
-- url     : https://prove2.me/theorems/c028f319-3a42-4a98-975f-d698f823f0f2
-- title:
--   Wrap: sim runs
-- statement:
--   If M puts out y on `pre x` within t steps, then the simulation ends on x with `post y` within t
--   steps, and all its states have size at most a·(|pre x| + 1) + a·t, where a is the constant of the
--   coding.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L102-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L102-L128

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}

theorem Wrap.sim_runs (K : Coding M) (pre post : List Bool → List Bool) {x y : List Bool} {t : ℕ} (h : Outputs M (pre x) y t) :
    (sim K pre post).Runs x t (K.a * ((pre x).length + 1) + K.a * t) (post y) := by sorry
