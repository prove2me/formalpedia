-- Prove2me | Theorems.Thm_Wrap_Arith_pow_le_rate
-- name    : Wrap.Arith.pow_le_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:52.775258+00:00
-- url     : https://prove2.me/theorems/ab238517-6dad-43a6-9225-8e4f3807427f
-- title:
--   Arith: pow le rate
-- statement:
--   (n+2)^D ≤ 2^{D·(64·n·r(n) + 256)} with r(n) = lg lg(n+4)/√(lg(n+4)), because n + 2 ≤ n + 4 =
--   2^{lg(n+4)}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L167-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L167-L175

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

theorem Wrap.Arith.pow_le_rate (D n : ℕ) : ((n : ℝ) + 2) ^ D ≤ (2 : ℝ) ^ ((D : ℝ) * (64 * ((n : ℝ) * SatK.rN 1 (1 / 2) n) + 256)) := by sorry
