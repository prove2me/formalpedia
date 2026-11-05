-- Prove2me | Theorems.Thm_Wrap_Conf_size_stack_le
-- name    : Wrap.Conf.size_stack_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:04:05.821207+00:00
-- url     : https://prove2.me/theorems/856f468d-7597-4faf-a12d-d9cba7e5a8ba
-- title:
--   Conf: size stack le
-- statement:
--   A stack of n symbols, as a list of numbers, has size at most n·(bound + 1) + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L300-L304
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L300-L304

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
variable (M : TM2ComputableAux Bool Bool)
variable [∀ i, Finite (M.tm.Γ i)]

theorem Wrap.Conf.size_stack_le (k : M.tm.K) (S : List (M.tm.Γ k)) : size (S.map (sym M k)) ≤ S.length * (bnd M + 1) + 1 := by sorry
