-- Prove2me | Theorems.Thm_Wrap_wraps_of_coding
-- name    : Wrap.wraps_of_coding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:34.073251+00:00
-- url     : https://prove2.me/theorems/8553effc-82f3-4760-b1d1-9215ea5b8661
-- title:
--   Wrap: wraps of coding
-- statement:
--   The composition lemma, from a coding: if the configurations of M have a coding, then for all
--   polynomial-time `pre`, `post` there are a machine N with finite alphabets and a number q such that,
--   whenever M puts out y on `pre x` within t steps, N puts out
--   `post y` on x within q·(t + |x| + 1)^q steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L156-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Sim.lean#L156-L167

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

theorem Wrap.wraps_of_coding {M : TM2ComputableAux Bool Bool} (K : Coding M) {pre post : List Bool → List Bool} (hpre : PolyT pre) (hpost : PolyT post) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ Wraps M pre post N q := by sorry
