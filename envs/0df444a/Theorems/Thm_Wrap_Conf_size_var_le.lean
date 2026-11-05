-- Prove2me | Theorems.Thm_Wrap_Conf_size_var_le
-- name    : Wrap.Conf.size_var_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:04:17.142826+00:00
-- url     : https://prove2.me/theorems/e5a05b1b-18c1-48cf-b8a0-33cf16f50292
-- title:
--   Conf: size var le
-- statement:
--   The number of a state has size at most the bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L150-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L150-L150

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
omit [∀ i, Finite (M.tm.Γ i)]

theorem Wrap.Conf.size_var_le (v : M.tm.σ) : size (num v) ≤ bnd M := by sorry
