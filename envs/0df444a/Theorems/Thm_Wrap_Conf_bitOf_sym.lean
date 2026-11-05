-- Prove2me | Theorems.Thm_Wrap_Conf_bitOf_sym
-- name    : Wrap.Conf.bitOf_sym
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:16.550513+00:00
-- url     : https://prove2.me/theorems/c29906a0-a21d-497b-b9f0-6ad715bfb676
-- title:
--   Conf: bit Of sym
-- statement:
--   The table gives back the bit of a symbol.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L273-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L273-L276

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

theorem Wrap.Conf.bitOf_sym (y : M.tm.Γ M.tm.k₁) : bitOf M (sym M M.tm.k₁ y) = M.outputAlphabet y := by sorry
