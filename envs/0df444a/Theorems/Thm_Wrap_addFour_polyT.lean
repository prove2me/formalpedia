-- Prove2me | Theorems.Thm_Wrap_addFour_polyT
-- name    : Wrap.addFour_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:05:22.033209+00:00
-- url     : https://prove2.me/theorems/7f6541a7-1563-4c3d-b7c7-40da317d8940
-- title:
--   Wrap: add Four poly T
-- statement:
--   Adding the four unit clauses is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L160-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L160-L162

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

theorem Wrap.addFour_polyT {α : Type} [Enc α] {d : α → ℕ × NCNF} (hd : PolyT d) : PolyT fun x => addFour (d x) := by sorry
