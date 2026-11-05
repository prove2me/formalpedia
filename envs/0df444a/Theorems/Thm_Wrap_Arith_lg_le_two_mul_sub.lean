-- Prove2me | Theorems.Thm_Wrap_Arith_lg_le_two_mul_sub
-- name    : Wrap.Arith.lg_le_two_mul_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:12.907666+00:00
-- url     : https://prove2.me/theorems/b9738b64-7e86-4f1c-96f2-e4d06dd4839d
-- title:
--   Arith: lg le two mul sub
-- statement:
--   lg t ≤ 2·(t − 1) for t ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L77-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L77-L82

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

theorem Wrap.Arith.lg_le_two_mul_sub {t : ℝ} (ht : 1 ≤ t) : lg t ≤ 2 * (t - 1) := by sorry
