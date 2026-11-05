-- Prove2me | Theorems.Thm_Wrap_Arith_rate_le_const_add
-- name    : Wrap.Arith.rate_le_const_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:03.585939+00:00
-- url     : https://prove2.me/theorems/10202188-df33-4b72-ab28-05632a3790ea
-- title:
--   Arith: rate le const add
-- statement:
--   For B ≥ 0, ε > 0 and any natural number n₀ ≥ 2^((8B/ε)^4): B·n·lg lg n/√(lg n) ≤ 8·B·n₀ + ε·n
--   for all n ≥ 4.
--   For n ≤ n₀ the first summand is enough, because lg lg n/√(lg n) ≤ 8; for n ≥ n₀ the second is
--   enough, because then B·lg lg n/√(lg n) ≤ ε.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L82-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L82-L121

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

theorem Wrap.Arith.rate_le_const_add {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) {n₀ : ℕ} (hn₀ : (2 : ℝ) ^ ((8 * B / ε) ^ 4) ≤ n₀) {n : ℕ} (hn : 4 ≤ n) :
    B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) ≤ 8 * B * n₀ + ε * n := by sorry
