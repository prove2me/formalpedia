-- Prove2me | Theorems.Thm_Wrap_everyMachineCanBeWrapped_of
-- name    : Wrap.everyMachineCanBeWrapped_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:28.370199+00:00
-- url     : https://prove2.me/theorems/c8e7222e-d31c-45d3-a62f-659a6c354899
-- title:
--   Wrap: every Machine Can Be Wrapped of
-- statement:
--   If every machine with finite alphabets has a coding of its configurations, then every such
--   machine can be given a polynomial-time front end and a polynomial-time last step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L171-L172
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L171-L172

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

theorem Wrap.everyMachineCanBeWrapped_of (h : ∀ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) → Nonempty (Coding M)) : EveryMachineCanBeWrapped := by sorry
