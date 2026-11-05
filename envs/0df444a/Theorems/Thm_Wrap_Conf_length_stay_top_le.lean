-- Prove2me | Theorems.Thm_Wrap_Conf_length_stay_top_le
-- name    : Wrap.Conf.length_stay_top_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:01.386193+00:00
-- url     : https://prove2.me/theorems/50bfa080-d268-4cd6-8d5d-7f2abaf00e00
-- title:
--   Conf: length stay top le
-- statement:
--   After a step on the tops alone a stack has at most 2d symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L126-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L126-L127

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)

theorem Wrap.Conf.length_stay_top_le (c : M.tm.Cfg) (k : M.tm.K) : ((stay M (top M c)).stk k).length ≤ 2 * dep M := by sorry
