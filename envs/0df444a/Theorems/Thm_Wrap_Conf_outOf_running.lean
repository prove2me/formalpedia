-- Prove2me | Theorems.Thm_Wrap_Conf_outOf_running
-- name    : Wrap.Conf.outOf_running
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:28:33.745001+00:00
-- url     : https://prove2.me/theorems/4939c780-7148-4ee8-b5ed-3650b74995fc
-- title:
--   Conf: out Of running
-- statement:
--   On a configuration that is not halted there is no output.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L294-L295
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L294-L295

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
variable [∀ i, Finite (M.tm.Γ i)]

theorem Wrap.Conf.outOf_running (c : M.tm.Cfg) (h : c.l ≠ none) : outOf M (repOf M c) = none := by sorry
