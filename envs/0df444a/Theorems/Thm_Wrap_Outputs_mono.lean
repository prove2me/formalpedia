-- Prove2me | Theorems.Thm_Wrap_Outputs_mono
-- name    : Wrap.Outputs.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:43:47.38924+00:00
-- url     : https://prove2.me/theorems/ad1c26c1-ebdc-4414-b7c9-d1c963bb7b1a
-- title:
--   Outputs: mono
-- statement:
--   A bound on the number of steps may be made larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L131-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L131-L133

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
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono

set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}

theorem Wrap.Outputs.mono {N : TM2ComputableAux Bool Bool} {x y : List Bool} {t t' : ℕ} (h : Outputs N x y t) (ht : t ≤ t') : Outputs N x y t' := by sorry
