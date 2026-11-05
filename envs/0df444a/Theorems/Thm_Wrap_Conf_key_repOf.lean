-- Prove2me | Theorems.Thm_Wrap_Conf_key_repOf
-- name    : Wrap.Conf.key_repOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:27:47.903905+00:00
-- url     : https://prove2.me/theorems/9952159a-6325-4cba-a01f-5ddc01ab9811
-- title:
--   Conf: key rep Of
-- statement:
--   Cutting the value of a configuration gives the value of the configuration made of the tops.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L177-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L177-L178

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

theorem Wrap.Conf.key_repOf (c : M.tm.Cfg) : key (dep M) (repOf M c) = repOf M (top M c) := by sorry
