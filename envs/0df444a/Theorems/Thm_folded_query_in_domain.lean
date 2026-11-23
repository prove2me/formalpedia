-- Prove2me | Theorems.Thm_folded_query_in_domain
-- name    : folded_query_in_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:57:35.136802+00:00
-- url     : https://prove2.me/theorems/62749f58-e71d-4073-90aa-7b2342bcb18d
-- title:
--   folded query in domain: folded query in domain
-- statement:
--   z^(i) is in D_i if z is in D_0
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L545-L556
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L545-L556

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem folded_query_in_domain {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (z : F) (hz : z ∈ P.D_0) (i : ℕ) :
    i ≤ P.num_foldings → folded_query P z i ∈ FRI_domain P i := by sorry
