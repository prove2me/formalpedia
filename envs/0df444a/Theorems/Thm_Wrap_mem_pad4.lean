-- Prove2me | Theorems.Thm_Wrap_mem_pad4
-- name    : Wrap.mem_pad4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:44:53.452673+00:00
-- url     : https://prove2.me/theorems/7568cf62-8da9-479f-ac8f-7012c9d780d9
-- title:
--   Wrap: mem pad4
-- statement:
--   A clause is in `pad4 φ` if and only if it is a clause of φ with its variables carried over, or
--   one of the four unit clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L45-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L45-L47

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

theorem Wrap.mem_pad4 {n : ℕ} {φ : Sat3.CNF n} {D : List (Sat3.Lit (n + 4))} :
    D ∈ pad4 φ ↔ (∃ C ∈ φ, (C.map fun l => (Fin.castAdd 4 l.1, l.2)) = D) ∨ ∃ j : Fin 4, [(Fin.natAdd n j, true)] = D := by sorry
