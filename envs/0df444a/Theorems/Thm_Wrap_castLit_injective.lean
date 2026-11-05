-- Prove2me | Theorems.Thm_Wrap_castLit_injective
-- name    : Wrap.castLit_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:28:57.924952+00:00
-- url     : https://prove2.me/theorems/f0db10df-679e-40ab-accf-aea78e22cff1
-- title:
--   Wrap: cast Lit injective
-- statement:
--   The map on literals inside `pad4`, which keeps the number of the variable and the sign, is
--   injective.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L38-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L38-L41

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

theorem Wrap.castLit_injective (n : ℕ) : Function.Injective fun l : Sat3.Lit n => ((Fin.castAdd 4 l.1, l.2) : Sat3.Lit (n + 4)) := by sorry
