-- Prove2me | Theorems.Thm_Wrap_Conf_size_nat_le
-- name    : Wrap.Conf.size_nat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:29:43.780995+00:00
-- url     : https://prove2.me/theorems/65226793-cd1a-4d9d-9ab7-187f1c7380b9
-- title:
--   Conf: size nat le
-- statement:
--   If n ≤ b, the size of n is at most the number of bits of b, plus 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L50-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L50-L51

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

theorem Wrap.Conf.size_nat_le {n b : ℕ} (h : n ≤ b) : size n ≤ Nat.size b + 1 := by sorry
