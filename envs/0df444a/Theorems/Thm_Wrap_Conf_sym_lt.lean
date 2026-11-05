-- Prove2me | Theorems.Thm_Wrap_Conf_sym_lt
-- name    : Wrap.Conf.sym_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:13.017167+00:00
-- url     : https://prove2.me/theorems/7abd695b-138f-4611-b886-fc23533460ae
-- title:
--   Conf: sym lt
-- statement:
--   The numbers of the symbols are below the number of all symbols of all stacks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L139-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L139-L139

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

theorem Wrap.Conf.sym_lt (k : M.tm.K) (x : M.tm.Γ k) : sym M k x < Nat.card (Σ k, M.tm.Γ k) := by sorry
