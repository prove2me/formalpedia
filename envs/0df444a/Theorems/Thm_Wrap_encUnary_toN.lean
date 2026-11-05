-- Prove2me | Theorems.Thm_Wrap_encUnary_toN
-- name    : Wrap.encUnary_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:05.515176+00:00
-- url     : https://prove2.me/theorems/ae53f503-c3de-44f4-964d-5d85c1b2f1ca
-- title:
--   Wrap: enc Unary to N
-- statement:
--   On w = ⌊log₂(2N)⌋ + 1 in unary and a formula over N names, with natural numbers as variables,
--   `encUnary` is the compact code at width 3.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L131-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L131-L132

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

theorem Wrap.encUnary_toN {N : ℕ} (ψ : Sat3.CNF N) : encUnary (List.replicate (Nat.log2 (2 * N) + 1) ()) (toN ψ) = MainTheoremForms.encC 3 ψ := by sorry
