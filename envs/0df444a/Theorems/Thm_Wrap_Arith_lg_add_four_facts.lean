-- Prove2me | Theorems.Thm_Wrap_Arith_lg_add_four_facts
-- name    : Wrap.Arith.lg_add_four_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:20.330925+00:00
-- url     : https://prove2.me/theorems/be08126e-482b-4576-85de-b26acafe65d7
-- title:
--   Arith: lg add four facts
-- statement:
--   lg(n+4) ≥ 2 and lg lg(n+4) ≥ 1, for every n ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L56-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L56-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_Wrap_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_Wrap_ArithRate
set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith

theorem Wrap.Arith.lg_add_four_facts (n : ℕ) : 2 ≤ lg ((n : ℝ) + 4) ∧ 1 ≤ lg (lg ((n : ℝ) + 4)) := by sorry
