-- Prove2me | Theorems.Thm_Wrap_Conf_size_initOf_le
-- name    : Wrap.Conf.size_initOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:28:49.788407+00:00
-- url     : https://prove2.me/theorems/8374caf9-70e6-43ae-9423-d412c2573b76
-- title:
--   Conf: size init Of le
-- statement:
--   The value of the start configuration is at most linear in the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L338-L348
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L338-L348

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

theorem Wrap.Conf.size_initOf_le (x : List Bool) :
    size (initOf M x) ≤ (2 * bnd M + (ks M).length * (bnd M + 3) + 1) * (x.length + 1) := by sorry
