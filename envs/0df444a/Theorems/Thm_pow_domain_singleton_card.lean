-- Prove2me | Theorems.Thm_pow_domain_singleton_card
-- name    : pow_domain_singleton_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:03:23.262525+00:00
-- url     : https://prove2.me/theorems/403a3676-4069-44ea-bc4b-a7ad2bd18d38
-- title:
--   pow domain singleton card: pow domain singleton card
-- statement:
--   The pow_domain of a singleton finset is a singleton.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L221-L222
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L221-L222

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem pow_domain_singleton_card {F : Type*} [CommMonoid F] [DecidableEq F] (x : F) (m : ℕ) :
    (pow_domain {x} m).card = 1 := by sorry
