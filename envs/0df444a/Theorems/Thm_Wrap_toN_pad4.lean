-- Prove2me | Theorems.Thm_Wrap_toN_pad4
-- name    : Wrap.toN_pad4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:04:41.184216+00:00
-- url     : https://prove2.me/theorems/e86d9dfa-2e83-4e04-80e6-6787bf207a3f
-- title:
--   Wrap: to N pad4
-- statement:
--   The padded formula, with natural numbers as variables, is φ with natural numbers as variables
--   and the four unit clauses on n, …, n + 3 behind it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L136-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L136-L138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode

theorem Wrap.toN_pad4 {n : ℕ} (φ : Sat3.CNF n) : toN (pad4 φ) = addFour (n, toN φ) := by sorry
