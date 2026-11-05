-- Prove2me | Theorems.Thm_Wrap_Conf_size_append
-- name    : Wrap.Conf.size_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:33:59.724712+00:00
-- url     : https://prove2.me/theorems/05e653cd-38f0-47e3-8c93-0ec9d81fec98
-- title:
--   Conf: size append
-- statement:
--   The sizes of two lists add up to the size of the joined list and 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L54-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L54-L55

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

theorem Wrap.Conf.size_append {α : Type} [HasSize α] (l l' : List α) : size (l ++ l') + 1 = size l + size l' := by sorry
