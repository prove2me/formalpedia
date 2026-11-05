-- Prove2me | Theorems.Thm_Wrap_Conf_size_sym_le
-- name    : Wrap.Conf.size_sym_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:27:30.612959+00:00
-- url     : https://prove2.me/theorems/895277da-ae1e-4e5b-9b18-01f736622f76
-- title:
--   Conf: size sym le
-- statement:
--   The number of a symbol has size at most the bound.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L153-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L153-L154

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

theorem Wrap.Conf.size_sym_le (k : M.tm.K) (x : M.tm.Γ k) : size (sym M k x) ≤ bnd M := by sorry
