-- Prove2me | Theorems.Thm_Wrap_Arith_rate_below
-- name    : Wrap.Arith.rate_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:03.748084+00:00
-- url     : https://prove2.me/theorems/b012e2f9-f304-4a9c-9996-0e97eda5db72
-- title:
--   Arith: rate below
-- statement:
--   For every B ≥ 0 and ε > 0 there is a c with 2^{B·n·lg lg n/√(lg n)} ≤ c·2^{εn} for all n ≥ 4:
--   take a natural number n₀ ≥ 2^((8B/ε)^4) and then c ≥ 2^(8·B·n₀).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L125-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L125-L133

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

theorem Wrap.Arith.rate_below {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ c : ℕ, ∀ n : ℕ, 4 ≤ n → (2 : ℝ) ^ (B * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := by sorry
