-- Prove2me | Theorems.Thm_Wrap_wrapped_time_le
-- name    : Wrap.wrapped_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:04.500112+00:00
-- url     : https://prove2.me/theorems/4b6fd3fa-bf58-4eea-9f14-65cdd21cc0ce
-- title:
--   Wrap: wrapped time le
-- statement:
--   For all q, C₁, C₂, a, d and every δ > 0 there is a c such that q·(⌊2^{C₁·min{m'/√(lg m'), n'·lg
--   lg n'/√(lg n')}}⌋ + C₂·L^{C₂} + X + 1)^q ≤ ⌊c·2^{δn}⌋ whenever m' ≥ 2, 4 ≤ n' ≤ n + 4 and L, X ≤
--   a·(n+2)^d.
--   The constant C₁ in the exponent and the constant C₂ in the polynomial need not be equal. The proof
--   does not use m' ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L206-L258
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L206-L258

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
open Arith

theorem Wrap.wrapped_time_le (q C₁ C₂ a d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℕ, ∀ (n m' n' L X : ℕ), 2 ≤ m' → 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((MainTheoremForms.timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ ⌊(c : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
