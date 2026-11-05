-- Prove2me | Theorems.Thm_Wrap_Conf_stay_eq_top
-- name    : Wrap.Conf.stay_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:03:51.685805+00:00
-- url     : https://prove2.me/theorems/176506e1-597b-4e91-ad47-1e5260c48802
-- title:
--   Conf: stay eq top
-- statement:
--   One step: do the step on the tops alone, and put the new tops in front of what lies below the
--   top d symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L121-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L121-L123

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

theorem Wrap.Conf.stay_eq_top (c : M.tm.Cfg) : stay M c =
    ⟨(stay M (top M c)).l, (stay M (top M c)).var, fun k => (stay M (top M c)).stk k ++ (c.stk k).drop (dep M)⟩ := by sorry
