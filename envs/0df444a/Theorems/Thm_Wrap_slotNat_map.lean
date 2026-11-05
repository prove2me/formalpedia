-- Prove2me | Theorems.Thm_Wrap_slotNat_map
-- name    : Wrap.slotNat_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:04:17.105857+00:00
-- url     : https://prove2.me/theorems/d0097264-008f-4a98-8949-27198156c563
-- title:
--   Wrap: slot Nat map
-- statement:
--   The number of a slot, with natural numbers as variables, is that of `Sat3.slot`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L126-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L126-L127

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode

theorem Wrap.slotNat_map {n : ℕ} (o : Option (Sat3.Lit n)) : slotNat (o.map fun l => (l.1.val, l.2)) = Sat3.slot o := by sorry
