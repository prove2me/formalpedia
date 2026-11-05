-- Prove2me | Theorems.Thm_Wrap_Arith_lg_div_sqrt_le
-- name    : Wrap.Arith.lg_div_sqrt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:44.74336+00:00
-- url     : https://prove2.me/theorems/03ba2d88-f470-4372-b9f1-33dc4c456501
-- title:
--   Arith: lg div sqrt le
-- statement:
--   lg y/√y ≤ 8/y^(1/4) for y > 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L71-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L71-L76

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

theorem Wrap.Arith.lg_div_sqrt_le {y : ℝ} (hy : 0 < y) : lg y / Real.sqrt y ≤ 8 / Real.sqrt (Real.sqrt y) := by sorry
