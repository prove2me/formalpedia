-- Prove2me | Theorems.Thm_Wrap_Arith_le_two_mul_two_rpow
-- name    : Wrap.Arith.le_two_mul_two_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:02.01439+00:00
-- url     : https://prove2.me/theorems/1684a2c9-903b-49ea-a855-54a89eccba6f
-- title:
--   Arith: le two mul two rpow
-- statement:
--   s ≤ 2·2^s for every real s ≥ 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L146-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L146-L152

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Definitions.Def_Wrap_Arith
set_option autoImplicit false
section
section
open Wrap
open MainTheoremForms
open Wrap.Arith

theorem Wrap.Arith.le_two_mul_two_rpow {s : ℝ} (hs : 0 ≤ s) : s ≤ 2 * (2 : ℝ) ^ s := by sorry
