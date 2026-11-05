-- Prove2me | Theorems.Thm_Wrap_Conf_outOf_halted
-- name    : Wrap.Conf.outOf_halted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:28:23.902098+00:00
-- url     : https://prove2.me/theorems/f689d951-fde7-49b1-9459-5f1cfd79a872
-- title:
--   Conf: out Of halted
-- statement:
--   On a halted configuration the output is the content of the output stack, as bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L290-L291
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L290-L291

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
variable [∀ i, Finite (M.tm.Γ i)]

theorem Wrap.Conf.outOf_halted (c : M.tm.Cfg) (h : c.l = none) : outOf M (repOf M c) = some ((c.stk M.tm.k₁).map M.outputAlphabet) := by sorry
