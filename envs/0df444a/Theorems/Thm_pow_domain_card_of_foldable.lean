-- Prove2me | Theorems.Thm_pow_domain_card_of_foldable
-- name    : pow_domain_card_of_foldable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:20:01.514863+00:00
-- url     : https://prove2.me/theorems/63cbbef0-8a3a-4784-938a-4215bf3f358e
-- title:
--   pow domain card of foldable: pow domain card of foldable
-- statement:
--   For a foldable domain D with |D| = m^k, the pow_domain has cardinality m^(k-1).
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L225-L259
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L225-L259

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem pow_domain_card_of_foldable {F : Type*} [Field F] [DecidableEq F]
    (D : Finset F) (H : Subgroup Fˣ) (a : Fˣ) (m k : ℕ) (hm : m > 0)
    (hD : (D : Set F) = (a • (H : Set Fˣ)).image (fun x ↦ ↑x))
    (hk : D.card = m ^ k) :
    (pow_domain D m).card = m ^ (k - 1) := by sorry
