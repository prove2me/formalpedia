-- Prove2me | Theorems.Thm_Wrap_length_encC
-- name    : Wrap.length_encC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:29:19.425763+00:00
-- url     : https://prove2.me/theorems/1ce8a178-8990-4bed-8187-e707902870b7
-- title:
--   Wrap: length enc C
-- statement:
--   The length of the compact code: k + w + 2 + m·k·w with w = ⌊log₂(2N)⌋ + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L184-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/FrontEnd.lean#L184-L191

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

theorem Wrap.length_encC (k : ℕ) {N : ℕ} (ψ : Sat3.CNF N) :
    (MainTheoremForms.encC k ψ).length = k + (Nat.log2 (2 * N) + 1) + 2 + ψ.length * (k * (Nat.log2 (2 * N) + 1)) := by sorry
