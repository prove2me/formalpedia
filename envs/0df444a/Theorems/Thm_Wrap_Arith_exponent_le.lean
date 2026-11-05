-- Prove2me | Theorems.Thm_Wrap_Arith_exponent_le
-- name    : Wrap.Arith.exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:21.283194+00:00
-- url     : https://prove2.me/theorems/ac54632c-3ce5-4e2e-b716-8ffd2d3e1b9f
-- title:
--   Arith: exponent le
-- statement:
--   n'·lg lg n'/√(lg n') ≤ (n+4)·lg lg(n+4)/√(lg(n+4)) for 4 ≤ n' ≤ n + 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L118-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L118-L129

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

theorem Wrap.Arith.exponent_le {n n' : ℕ} (hn' : 4 ≤ n') (hnn : n' ≤ n + 4) :
    (n' : ℝ) * lg (lg n') / Real.sqrt (lg n') ≤ ((n : ℝ) + 4) * SatK.rN 1 (1 / 2) n := by sorry
