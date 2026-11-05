-- Prove2me | Theorems.Thm_Wrap_Arith_div_sqrt_lg_mono
-- name    : Wrap.Arith.div_sqrt_lg_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:43:08.532827+00:00
-- url     : https://prove2.me/theorems/455bde44-e9cb-40c8-a3ea-53465538a7b4
-- title:
--   Arith: div sqrt lg mono
-- statement:
--   x/√(lg x) ≤ y/√(lg y) for 2 ≤ x ≤ y.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L109-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/ArithRate.lean#L109-L115

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

theorem Wrap.Arith.div_sqrt_lg_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) : x / Real.sqrt (lg x) ≤ y / Real.sqrt (lg y) := by sorry
