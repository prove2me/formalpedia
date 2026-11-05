-- Prove2me | Theorems.Thm_Wrap_Arith_poly_below
-- name    : Wrap.Arith.poly_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:05.382228+00:00
-- url     : https://prove2.me/theorems/cafd51b8-ee75-45b0-a86a-fb6a9a048599
-- title:
--   Arith: poly below
-- statement:
--   For every D and ε > 0 there is a c with (n+2)^D ≤ c·2^{εn} for all n. With K = D + 1: n + 2 ≤
--   (2K/ε + 2)·2^{εn/K}, and the K-th power of the right side is (2K/ε + 2)^K·2^{εn}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L156-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L156-L179

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

theorem Wrap.Arith.poly_below (D : ℕ) {ε : ℝ} (hε : 0 < ε) : ∃ c : ℕ, ∀ n : ℕ, ((n : ℝ) + 2) ^ D ≤ (c : ℝ) * (2 : ℝ) ^ (ε * n) := by sorry
