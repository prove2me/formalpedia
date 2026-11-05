-- Prove2me | Theorems.Thm_Wrap_wrapped_time_le_rate
-- name    : Wrap.wrapped_time_le_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:18.886397+00:00
-- url     : https://prove2.me/theorems/62dc0ec8-9f00-4d7b-ace7-5d79a287cf2c
-- title:
--   Wrap: wrapped time le rate
-- statement:
--   For all q, C₁, C₂, a, d there is a c such that q·(⌊2^{C₁·min{m'/√(lg m'), n'·lg lg n'/√(lg
--   n')}}⌋ + C₂·L^{C₂} + X + 1)^q ≤ ⌊c·2^{c·9·n·lg lg(n+4)/√(lg(n+4))}⌋ whenever m' ≥ 2, 4 ≤ n' ≤ n + 4
--   and L, X ≤ a·(n+2)^d.
--   The proof does not use m' ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L187-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L187-L261

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
open Arith

theorem Wrap.wrapped_time_le_rate (q C₁ C₂ a d : ℕ) :
    ∃ c : ℕ, ∀ (n m' n' L X : ℕ), 2 ≤ m' → 4 ≤ n' → n' ≤ n + 4 → L ≤ a * (n + 2) ^ d → X ≤ a * (n + 2) ^ d →
      q * ((MainTheoremForms.timeMin3 C₁ m' n' + C₂ * L ^ C₂) + X + 1) ^ q ≤ SatM.boundNK (SatK.rN 1 (1 / 2)) c 3 n := by sorry
