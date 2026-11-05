-- Prove2me | Theorems.Thm_Wrap_Arith_rate_eq
-- name    : Wrap.Arith.rate_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:49.2097+00:00
-- url     : https://prove2.me/theorems/42d5760f-a12d-4699-b113-6ecefe1733d2
-- title:
--   Arith: rate eq
-- statement:
--   The rate with exponents 1 and 1/2, written with lg and a square root: lg lg(n+4)/√(lg(n+4)).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L50-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L50-L53

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

theorem Wrap.Arith.rate_eq (n : ℕ) : SatK.rN 1 (1 / 2) n = lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4)) := by sorry
