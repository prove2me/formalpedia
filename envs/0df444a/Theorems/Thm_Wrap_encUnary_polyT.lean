-- Prove2me | Theorems.Thm_Wrap_encUnary_polyT
-- name    : Wrap.encUnary_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:13.5141+00:00
-- url     : https://prove2.me/theorems/c1e2755c-e23d-4430-a736-396b0a89d19a
-- title:
--   Wrap: enc Unary poly T
-- statement:
--   Writing the compact code at width 3 is polynomial-time, with the number of bits of a slot in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L166-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L166-L171

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

theorem Wrap.encUnary_polyT {α : Type} [Enc α] {w : α → List Unit} {F : α → NCNF} (hw : PolyT w) (hF : PolyT F) : PolyT fun x => encUnary (w x) (F x) := by sorry
