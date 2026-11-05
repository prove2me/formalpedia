-- Prove2me | Theorems.Thm_Wrap_Conf_nxt_caseOf
-- name    : Wrap.Conf.nxt_caseOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:04:03.556044+00:00
-- url     : https://prove2.me/theorems/06be6f89-3c78-4511-9759-b537e54c03b4
-- title:
--   Conf: nxt case Of
-- statement:
--   The step on the tops alone, as the table of the machine has it, is the step of the configuration
--   made of the tops.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L113-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L113-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_CodingExists
set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)

theorem Wrap.Conf.nxt_caseOf (c : M.tm.Cfg) : nxt M (caseOf M c) = stay M (top M c) := by sorry
