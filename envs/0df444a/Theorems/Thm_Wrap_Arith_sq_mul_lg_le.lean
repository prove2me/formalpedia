-- Prove2me | Theorems.Thm_Wrap_Arith_sq_mul_lg_le
-- name    : Wrap.Arith.sq_mul_lg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:17.878121+00:00
-- url     : https://prove2.me/theorems/59f67487-be5a-49b3-834b-94f379d6aeaf
-- title:
--   Arith: sq mul lg le
-- statement:
--   x²·lg y ≤ y²·lg x for 2 ≤ x ≤ y. With t = y/x: lg y = lg x + lg t ≤ lg x + 2(t−1) ≤ t²·lg x,
--   because lg x ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L91-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L91-L106

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

theorem Wrap.Arith.sq_mul_lg_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : x ^ 2 * lg y ≤ y ^ 2 * lg x := by sorry
