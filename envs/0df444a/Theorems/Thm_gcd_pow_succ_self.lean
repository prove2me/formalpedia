-- Prove2me | Theorems.Thm_gcd_pow_succ_self
-- name    : gcd_pow_succ_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:03:14.337663+00:00
-- url     : https://prove2.me/theorems/0d4a2853-608a-49c2-be90-329643c06fef
-- title:
--   gcd pow succ self: gcd pow succ self
-- statement:
--   gcd(m^(k+1), m) = m for any m and k.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L217-L218
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L217-L218

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem gcd_pow_succ_self (m k : ℕ) : Nat.gcd (m ^ (k + 1)) m = m := by sorry
