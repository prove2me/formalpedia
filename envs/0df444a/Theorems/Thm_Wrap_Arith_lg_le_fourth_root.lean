-- Prove2me | Theorems.Thm_Wrap_Arith_lg_le_fourth_root
-- name    : Wrap.Arith.lg_le_fourth_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:43.197657+00:00
-- url     : https://prove2.me/theorems/18c9988a-f53a-42ac-b148-1471155e9104
-- title:
--   Arith: lg le fourth root
-- statement:
--   lg y ≤ 8·y^(1/4) for y > 0; the fourth root is written as a square root of a square root.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L54-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L54-L68

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

theorem Wrap.Arith.lg_le_fourth_root {y : ℝ} (hy : 0 < y) : lg y ≤ 8 * Real.sqrt (Real.sqrt y) := by sorry
