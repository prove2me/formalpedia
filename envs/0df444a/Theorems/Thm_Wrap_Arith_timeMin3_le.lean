-- Prove2me | Theorems.Thm_Wrap_Arith_timeMin3_le
-- name    : Wrap.Arith.timeMin3_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:42.70336+00:00
-- url     : https://prove2.me/theorems/cf14741d-322c-4b11-b0a8-fe67d4c31ce7
-- title:
--   Arith: time Min3 le
-- statement:
--   The time with the minimum of the two exponents is at most the power of 2 with the exponent in n
--   alone: ⌊2^{C·min{m/√(lg m), n·lg lg n/√(lg n)}}⌋ ≤ 2^{C·n·lg lg n/√(lg n)}. No hypothesis on C, m,
--   n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L138-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L138-L141

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

theorem Wrap.Arith.timeMin3_le (C m n : ℕ) : (timeMin3 C m n : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) := by sorry
