-- Prove2me | Theorems.Thm_Wrap_exists_bound
-- name    : Wrap.exists_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:46.471904+00:00
-- url     : https://prove2.me/theorems/aa9f3b31-6e16-47d1-97b5-422e74054ef8
-- title:
--   Wrap: exists bound
-- statement:
--   The numbers: for all q₀, a, c there is a q such that q₀·(t + 1)·(n + (a·(p + 1) + a·t) + 1)^q₀ ≤
--   q·(t + n + 1)^q whenever p ≤ c·(3n + 3)^c. (3n + 3 bounds the length of the word that stands for a
--   bit string of length n, plus 1; `pre` is polynomial in that length.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L138-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L138-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_Wrap_Sim
set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}

theorem Wrap.exists_bound (q₀ a c : ℕ) : ∃ q : ℕ, ∀ t n p : ℕ, p ≤ c * (3 * n + 2 + 1) ^ c →
    q₀ * (t + 1) * (n + (a * (p + 1) + a * t) + 1) ^ q₀ ≤ q * (t + n + 1) ^ q := by sorry
