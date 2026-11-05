-- Prove2me | Theorems.Thm_Wrap_Arith_poly_part_le
-- name    : Wrap.Arith.poly_part_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:03:36.099657+00:00
-- url     : https://prove2.me/theorems/b33a5214-e5dc-4272-a9bd-a2aa3c280245
-- title:
--   Arith: poly part le
-- statement:
--   If L and X are at most a·(n+2)^d, then C·L^C + X + 1 ≤ (C·a^C + a + 1)·(n+2)^{dC+d}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L182-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Arith.lean#L182-L193

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

theorem Wrap.Arith.poly_part_le (C a d : ℕ) {n L X : ℕ} (hL : L ≤ a * (n + 2) ^ d) (hX : X ≤ a * (n + 2) ^ d) :
    C * L ^ C + X + 1 ≤ (C * a ^ C + a + 1) * (n + 2) ^ (d * C + d) := by sorry
