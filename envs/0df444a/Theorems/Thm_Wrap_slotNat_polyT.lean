-- Prove2me | Theorems.Thm_Wrap_slotNat_polyT
-- name    : Wrap.slotNat_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:04:32.505192+00:00
-- url     : https://prove2.me/theorems/c10732aa-8aba-4b5d-af49-60a95c498132
-- title:
--   Wrap: slot Nat poly T
-- statement:
--   The number of a slot is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L155-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L155-L157

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

theorem Wrap.slotNat_polyT {α : Type} [Enc α] {o : α → Option (ℕ × Bool)} (ho : PolyT o) : PolyT fun x => slotNat (o x) := by sorry
