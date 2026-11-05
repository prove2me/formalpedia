-- Prove2me | Theorems.Thm_Wrap_everyMachineCanBeWrapped
-- name    : Wrap.everyMachineCanBeWrapped
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:46:46.843001+00:00
-- url     : https://prove2.me/theorems/5608ae91-cf7c-48c4-b7aa-d0c15f89cfb7
-- title:
--   Wrap: every Machine Can Be Wrapped
-- statement:
--   Every machine with finite alphabets can be given a polynomial-time front end and a
--   polynomial-time last step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Main.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Main.lean#L39-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_Wrap_Sim
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_WidthThree_Rates
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_Wrap_Main
set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal

theorem Wrap.everyMachineCanBeWrapped : EveryMachineCanBeWrapped := by sorry
