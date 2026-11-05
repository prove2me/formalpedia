-- Prove2me | Theorems.Thm_Wrap_occurs_pad4
-- name    : Wrap.occurs_pad4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:08.843437+00:00
-- url     : https://prove2.me/theorems/6a1203d0-bb6f-4015-b856-3d7d6590612d
-- title:
--   Wrap: occurs pad4
-- statement:
--   Each of the four new variables occurs in `pad4 φ`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L55-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L55-L56

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

theorem Wrap.occurs_pad4 {n : ℕ} (φ : Sat3.CNF n) (j : Fin 4) : MainTheoremForms.Occurs (pad4 φ) (Fin.natAdd n j) := by sorry
