-- Prove2me | Theorems.Thm_units_smul_eq_mul
-- name    : units_smul_eq_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:01:23.288305+00:00
-- url     : https://prove2.me/theorems/743a284e-bcd2-425b-8dc6-bc5b43a64f1e
-- title:
--   units smul eq mul: units smul eq mul
-- statement:
--   For Fˣ, the scalar action a • x equals multiplication a * x.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L179-L180
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L179-L180

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem units_smul_eq_mul {F : Type*} [Field F] (a x : Fˣ) : a • x = a * x := by sorry
