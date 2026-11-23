-- Prove2me | Theorems.Thm_pow_domain_is_coset
-- name    : pow_domain_is_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T09:03:35.534424+00:00
-- url     : https://prove2.me/theorems/0b144a5c-6d2b-47d7-85bc-0932af8eddd2
-- title:
--   pow domain is coset: pow domain is coset
-- statement:
--   The power image of a foldable set is a coset
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L448-L472
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L448-L472

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem pow_domain_is_coset {F : Type*} [Field F] [DecidableEq F] {D : Finset F} {m : ℕ}
    (h : IsFoldable D m) :
    ∃ (H' : Subgroup Fˣ) (a' : Fˣ),
      (pow_domain D m : Set F) = (a' • (H' : Set Fˣ)).image (fun (x : Fˣ) ↦ (x : F)) := by sorry
