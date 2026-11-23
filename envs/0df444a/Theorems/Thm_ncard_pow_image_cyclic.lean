-- Prove2me | Theorems.Thm_ncard_pow_image_cyclic
-- name    : ncard_pow_image_cyclic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:54:17.118648+00:00
-- url     : https://prove2.me/theorems/1fbdd235-5a0c-44fb-bb6c-8e60059e8c55
-- title:
--   ncard pow image cyclic: ncard pow image cyclic
-- statement:
--   For a finite cyclic subgroup H = ⟨g⟩, the power image has ncard = ncard H / gcd (ncard H) m.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L136-L142
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L136-L142

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem ncard_pow_image_cyclic {G : Type*} [Group G] (H : Subgroup G) (g : G)
    (hg : H = Subgroup.zpowers g) (m : ℕ) (hH_finite : Set.Finite (H : Set G)) :
    (Set.image (fun x ↦ x ^ m) (H : Set G)).ncard =
    (H : Set G).ncard / Nat.gcd (H : Set G).ncard m := by sorry
