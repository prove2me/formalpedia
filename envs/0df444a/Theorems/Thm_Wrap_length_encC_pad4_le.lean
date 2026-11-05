-- Prove2me | Theorems.Thm_Wrap_length_encC_pad4_le
-- name    : Wrap.length_encC_pad4_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:06:06.046219+00:00
-- url     : https://prove2.me/theorems/f786480b-71d8-402b-9763-a6cc1747314a
-- title:
--   Wrap: length enc C pad4 le
-- statement:
--   Both codes are polynomially long in n: the compact code of the padded formula and the plain code
--   of φ have at most a·(n + 2)^d bits, for every 3-CNF φ on n variables without repeated clauses. The
--   proof takes a = 100 and d = 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L196-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L196-L210

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Math_Formula
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_FrontEnd
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Wrap
open Groundwork Groundwork.Decode

theorem Wrap.length_encC_pad4_le : ∃ a d : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ →
    (MainTheoremForms.encC 3 (pad4 φ)).length ≤ a * (n + 2) ^ d ∧ (Sat3.enc φ).length ≤ a * (n + 2) ^ d := by sorry
