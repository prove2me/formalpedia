-- Prove2me | Theorems.Thm_Wrap_Conf_size_repOf_le
-- name    : Wrap.Conf.size_repOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:28:36.492281+00:00
-- url     : https://prove2.me/theorems/4d5d013f-9ba6-4dd5-84ae-ab5a9d4e32ab
-- title:
--   Conf: size rep Of le
-- statement:
--   If every stack of c has at most n symbols, the value of c has size at most 2·bnd + (number of
--   stacks)·(n·(bnd + 1) + 2) + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L308-L317
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L308-L317

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
variable [∀ i, Finite (M.tm.Γ i)]

theorem Wrap.Conf.size_repOf_le (c : M.tm.Cfg) (n : ℕ) (h : ∀ k, (c.stk k).length ≤ n) :
    size (repOf M c) ≤ 2 * bnd M + ((ks M).length * (n * (bnd M + 1) + 1 + 1) + 1) := by sorry
